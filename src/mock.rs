//! Mock radio implementation for testing.
//!
//! This module provides a transaction-based mock radio that can be used for testing
//! code that depends on radio traits. It follows patterns similar to [`embedded-hal-mock`].
//!
//! [`embedded-hal-mock`]: https://docs.rs/embedded-hal-mock
//!
//! # Design
//!
//! The mock is generic over:
//! - `I`: Info type (receive metadata like RSSI, LQI)
//! - `S`: State type (radio states like Idle, Transmit, Receive)
//! - `E`: Error type (operation errors)
//! - `D`: Delay type (must implement `embedded_hal_async::delay::DelayNs`)
//!
//! The delay type is specified at compile time and doesn't require initialization.
//! Delay instances are created only when needed using the `Default` trait.
//!
//! # Example
//!
//! ```
//! use embedded_radio_async::mock::{Mock, Transaction};
//! use embedded_radio_async::Transmit;
//!
//! // Define your test types
//! #[derive(Debug, Clone, PartialEq)]
//! struct TestInfo { rssi: i16 }
//!
//! #[derive(Debug, Clone, PartialEq)]
//! enum TestState { Idle, Tx, Rx }
//!
//! #[derive(Debug, Clone, PartialEq)]
//! enum TestError { Io }
//!
//! # #[derive(Debug, Clone, Copy, Default)]
//! # struct TestDelay;
//! # impl embedded_hal_async::delay::DelayNs for TestDelay {
//! #     async fn delay_ns(&mut self, _ns: u32) {}
//! # }
//! # async fn example() -> Result<(), TestError> {
//! // Specify delay type in the Mock type, no need to pass it to new()
//! let mut radio: Mock<TestInfo, TestState, TestError, TestDelay> = Mock::new(&[
//!     Transaction::transmit(&[0xAA, 0xBB]),
//! ]);
//!
//! radio.transmit(&[0xAA, 0xBB]).await?;
//! radio.done();
//! # Ok(())
//! # }
//! ```

use crate::{Dbm, Power, Receive, State, Transmit};
use core::fmt::Debug;
use core::marker::PhantomData;
use embedded_hal_async::delay::DelayNs;
use heapless::Vec as HVec;

/// Maximum packet size for mock transactions.
const MAX_PACKET_SIZE: usize = 256;

/// Maximum number of transactions that can be queued in a mock.
///
/// This limit is necessary for `no_std` compatibility. 32 transactions should be
/// sufficient for most test scenarios.
const MAX_TRANSACTIONS: usize = 32;

/// Type alias for packet data storage
type PacketData = HVec<u8, MAX_PACKET_SIZE>;

/// Type alias for transaction queue
type TransactionQueue<I, S, E> = HVec<Transaction<I, S, E>, MAX_TRANSACTIONS>;

/// A transaction represents an expected operation on the mock radio.
///
/// The transaction is generic over:
/// - `I`: Info type (receive metadata)
/// - `S`: State type (radio states)
/// - `E`: Error type (operation errors)
///
/// Data is stored in fixed-capacity [`heapless::Vec`] with [`MAX_PACKET_SIZE`] capacity.
/// This allows the mock to work in `no_std` environments without requiring allocations.
///
/// Each transaction can include a delay that will be executed before returning from
/// the operation. This is useful for testing timeouts and `select!` behavior.
#[derive(Debug, Clone, PartialEq)]
pub struct Transaction<I, S, E>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq,
{
    request: Request<S>,
    response: Response<I, S, E>,
    /// Delay in nanoseconds to execute before returning (0 = no delay)
    delay_ns: u32,
}

impl<I, S, E> Transaction<I, S, E>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq,
{
    /// Helper to create packet data from a slice
    fn make_packet(data: &[u8]) -> PacketData {
        let mut vec = PacketData::new();
        vec.extend_from_slice(data)
            .expect("packet exceeds MAX_PACKET_SIZE");
        vec
    }

    /// Helper to create a basic transaction
    fn new(request: Request<S>, response: Response<I, S, E>) -> Self {
        Self {
            request,
            response,
            delay_ns: 0,
        }
    }

    /// Create a transmit transaction
    ///
    /// # Panics
    ///
    /// Panics if `data` exceeds [`MAX_PACKET_SIZE`] (256 bytes).
    pub fn transmit(data: &[u8]) -> Self {
        Self::new(Request::Transmit(Self::make_packet(data)), Response::Ok)
    }

    /// Create a listen transaction
    pub fn listen() -> Self {
        Self::new(Request::Listen, Response::Ok)
    }

    /// Create a receive transaction
    ///
    /// # Panics
    ///
    /// Panics if `data` exceeds [`MAX_PACKET_SIZE`] (256 bytes).
    pub fn receive(data: &[u8], info: I) -> Self {
        Self::new(
            Request::Receive,
            Response::Received(Self::make_packet(data), info),
        )
    }

    /// Create a set_power transaction
    pub fn set_power(power: Dbm) -> Self {
        Self::new(Request::SetPower(power), Response::Ok)
    }

    /// Create a get_state transaction that returns a state
    pub fn get_state(state: S) -> Self {
        Self::new(Request::GetState, Response::State(state))
    }

    /// Create a set_state transaction
    pub fn set_state(state: S) -> Self {
        Self::new(Request::SetState(state), Response::Ok)
    }

    /// Create a delay transaction
    ///
    /// This creates a transaction that will execute a delay.
    /// The delay is executed using the Mock's configured delay implementation.
    pub fn delay(duration: core::time::Duration) -> Self {
        let delay_ns = duration.as_nanos() as u32;
        Self {
            request: Request::DelayNs(delay_ns),
            response: Response::Ok,
            delay_ns,
        }
    }

    /// Add an error to this transaction.
    ///
    /// This will cause the operation to return an error instead of succeeding.
    ///
    /// # Example
    ///
    /// ```
    /// use embedded_radio_async::mock::Transaction;
    ///
    /// # #[derive(Debug, Clone, PartialEq)] struct TestInfo { rssi: i16 }
    /// # #[derive(Debug, Clone, PartialEq)] enum TestState { Idle }
    /// # #[derive(Debug, Clone, PartialEq)] enum TestError { Timeout }
    /// type TestTransaction = Transaction<TestInfo, TestState, TestError>;
    ///
    /// // Transmit operation that fails with timeout
    /// let transaction = TestTransaction::transmit(&[0xAA, 0xBB])
    ///     .with_error(TestError::Timeout);
    /// ```
    pub fn with_error(mut self, error: E) -> Self {
        // Only replace response if it was Ok or a successful response
        // This preserves the data/info for receive transactions
        match self.response {
            Response::Ok | Response::State(_) | Response::Received(_, _) => {
                self.response = Response::Err(error);
            }
            Response::Err(_) => {
                // Already has an error, replace it
                self.response = Response::Err(error);
            }
        }
        self
    }

    /// Add a delay to this transaction.
    ///
    /// The delay will be executed before the operation returns. This is useful
    /// for testing timeouts and `select!` behavior.
    ///
    /// # Example
    ///
    /// ```
    /// use embedded_radio_async::mock::Transaction;
    /// use core::time::Duration;
    ///
    /// # #[derive(Debug, Clone, PartialEq)] struct TestInfo { rssi: i16 }
    /// # #[derive(Debug, Clone, PartialEq)] enum TestState { Idle }
    /// # #[derive(Debug, Clone, PartialEq)] enum TestError { Io }
    /// type TestTransaction = Transaction<TestInfo, TestState, TestError>;
    ///
    /// // Listen operation that takes 100ms
    /// let transaction = TestTransaction::listen()
    ///     .with_delay(Duration::from_millis(100));
    /// ```
    pub fn with_delay(mut self, duration: core::time::Duration) -> Self {
        self.delay_ns = duration.as_nanos() as u32;
        self
    }
}

/// Request types for mock operations
#[derive(Debug, Clone, PartialEq)]
enum Request<S> {
    Transmit(PacketData),
    Listen,
    Receive,
    SetPower(Dbm),
    GetState,
    SetState(S),
    DelayNs(u32),
}

/// Response types for mock operations
#[derive(Debug, Clone, PartialEq)]
enum Response<I, S, E> {
    Ok,
    State(S),
    Received(PacketData, I),
    Err(E),
}


/// Mock radio device for testing.
///
/// This mock uses a transaction-based approach where expected operations are queued
/// and verified as methods are called.
///
/// The mock is generic over:
/// - `I`: Info type (receive metadata like RSSI, LQI)
/// - `S`: State type (radio states like Idle, Transmit, Receive)
/// - `E`: Error type (operation errors)
/// - `D`: Delay implementation (must implement `embedded_hal_async::delay::DelayNs` + `Default`)
///
/// The delay type `D` is specified at the type level and doesn't require initialization
/// in the constructor. Delay instances are created on-demand when needed.
///
/// # Example
///
/// ```
/// use embedded_radio_async::mock::{Mock, Transaction};
/// use embedded_radio_async::{Transmit, Receive};
/// use core::time::Duration;
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct TestInfo { rssi: i16 }
///
/// #[derive(Debug, Clone, PartialEq)]
/// enum TestState { Idle }
///
/// #[derive(Debug, Clone, PartialEq)]
/// enum TestError { Io }
///
/// # #[derive(Debug, Clone, Copy, Default)]
/// # struct TestDelay;
/// # impl embedded_hal_async::delay::DelayNs for TestDelay {
/// #     async fn delay_ns(&mut self, _ns: u32) {}
/// # }
/// # async fn example() -> Result<(), TestError> {
/// // Delay type specified at type level, not in constructor
/// let mut radio: Mock<TestInfo, TestState, TestError, TestDelay> = Mock::new(&[
///     Transaction::transmit(&[0xAA, 0xBB]),
///     Transaction::listen().with_delay(Duration::from_millis(100)),
///     Transaction::receive(&[0xCC, 0xDD], TestInfo { rssi: -50 }),
/// ]);
///
/// // Use the radio
/// radio.transmit(&[0xAA, 0xBB]).await?;
/// radio.listen().await?;  // Will delay 100ms before returning
///
/// let mut buffer = [0u8; 10];
/// let (len, info) = radio.receive(&mut buffer).await?;
///
/// assert_eq!(len, 2);
/// assert_eq!(&buffer[..2], &[0xCC, 0xDD]);
/// assert_eq!(info.rssi, -50);
///
/// // Verify all transactions were consumed
/// radio.done();
/// # Ok(())
/// # }
/// ```
pub struct Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq,
    D: DelayNs + Default,
{
    transactions: TransactionQueue<I, S, E>,
    index: usize,
    delay: PhantomData<D>,
}

impl<I, S, E, D> Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq,
    D: DelayNs + Default,
{
    /// Create a new mock radio with expected transactions
    ///
    /// The delay type `D` is specified in the Mock type parameter and must
    /// implement `Default`. The delay is not initialized here but created
    /// on-demand when needed for actual delays.
    ///
    /// # Panics
    ///
    /// Panics if `transactions` exceeds [`MAX_TRANSACTIONS`] (32 transactions).
    pub fn new(transactions: &[Transaction<I, S, E>]) -> Self {
        let mut queue = TransactionQueue::new();
        queue.extend_from_slice(transactions)
            .expect("too many transactions, exceeds MAX_TRANSACTIONS");
        Self {
            transactions: queue,
            index: 0,
            delay: PhantomData,
        }
    }

    /// Verify that all transactions have been consumed
    ///
    /// This method should be called at the end of a test to ensure all
    /// expected operations were performed.
    ///
    /// # Panics
    ///
    /// Panics if there are remaining unconsumed transactions.
    pub fn done(self) {
        let remaining = self.transactions.len() - self.index;
        assert!(
            remaining == 0,
            "Not all transactions were consumed. Remaining: {} transaction(s)",
            remaining
        );
    }

    /// Get the next expected transaction
    fn next(&mut self) -> Option<&Transaction<I, S, E>> {
        if self.index < self.transactions.len() {
            let transaction = &self.transactions[self.index];
            self.index += 1;
            Some(transaction)
        } else {
            None
        }
    }

    /// Execute a delay if needed
    async fn execute_delay(&self, delay_ns: u32) {
        if delay_ns > 0 {
            let mut delay = D::default();
            delay.delay_ns(delay_ns).await;
        }
    }

    /// Verify data matches expected value
    fn verify_data(actual: &[u8], expected: &[u8]) {
        assert_eq!(
            actual, expected,
            "Data mismatch:\n  expected: {:02X?}\n  actual:   {:02X?}",
            expected, actual
        );
    }

    /// Verify value matches expected value
    fn verify<T: PartialEq + Debug>(actual: &T, expected: &T, name: &str) {
        assert_eq!(
            actual, expected,
            "{} mismatch:\n  expected: {:?}\n  actual:   {:?}",
            name, expected, actual
        );
    }
}

impl<I, S, E, D> DelayNs for Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq,
    D: DelayNs + Default,
{
    async fn delay_ns(&mut self, ns: u32) {
        let delay_ns = {
            let n = self.next().expect("no expectation for delay_ns call");
            assert_eq!(&n.request, &Request::DelayNs(ns));
            n.delay_ns
        };

        // Execute the configured delay
        self.execute_delay(delay_ns).await;
    }
}

impl<I, S, E, D> Transmit for Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq + 'static,
    D: DelayNs + Default,
{
    type Error = E;

    async fn transmit(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for Transmit::transmit call");

            match &n.request {
                Request::Transmit(expected) => Self::verify_data(data, &expected[..]),
                _ => panic!(
                    "Expected Transmit transaction, got {:?}",
                    core::mem::discriminant(&n.request)
                ),
            }

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::Ok => Ok(()),
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }
}

impl<I, S, E, D> Receive for Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq + 'static,
    D: DelayNs + Default,
{
    type Error = E;
    type Info = I;

    async fn listen(&mut self) -> Result<(), Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for Receive::listen call");

            assert_eq!(
                &n.request,
                &Request::Listen,
                "Expected Listen transaction"
            );

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::Ok => Ok(()),
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }

    async fn receive(&mut self, buffer: &mut [u8]) -> Result<(usize, Self::Info), Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for Receive::receive call");

            assert_eq!(
                &n.request,
                &Request::Receive,
                "Expected Receive transaction"
            );

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::Received(data, info) => {
                let len = data.len().min(buffer.len());
                buffer[..len].copy_from_slice(&data[..len]);
                Ok((len, info.clone()))
            }
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }
}

impl<I, S, E, D> Power for Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq + 'static,
    D: DelayNs + Default,
{
    type Error = E;

    async fn set_power(&mut self, power: Dbm) -> Result<(), Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for Power::set_power call");

            match &n.request {
                Request::SetPower(expected) => Self::verify(&power, expected, "Power"),
                _ => panic!(
                    "Expected SetPower transaction, got {:?}",
                    core::mem::discriminant(&n.request)
                ),
            }

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::Ok => Ok(()),
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }
}

impl<I, S, E, D> State for Mock<I, S, E, D>
where
    I: Debug + Clone + PartialEq,
    S: Debug + Clone + PartialEq,
    E: Debug + Clone + PartialEq + 'static,
    D: DelayNs + Default,
{
    type Error = E;
    type State = S;

    async fn set_state(&mut self, state: Self::State) -> Result<(), Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for State::set_state call");

            match &n.request {
                Request::SetState(expected) => Self::verify(&state, expected, "State"),
                _ => panic!(
                    "Expected SetState transaction, got {:?}",
                    core::mem::discriminant(&n.request)
                ),
            }

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::Ok => Ok(()),
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }

    async fn get_state(&mut self) -> Result<Self::State, Self::Error> {
        let (response, delay_ns) = {
            let n = self
                .next()
                .expect("no expectation for State::get_state call");

            assert_eq!(
                &n.request,
                &Request::GetState,
                "Expected GetState transaction"
            );

            (n.response.clone(), n.delay_ns)
        };

        // Execute delay if specified
        self.execute_delay(delay_ns).await;

        match &response {
            Response::State(s) => Ok(s.clone()),
            Response::Err(e) => Err(e.clone()),
            _ => unreachable!(),
        }
    }
}
#[cfg(all(feature = "std", test))]
mod tests {
    use super::*;

    // Test infrastructure - types that represent typical radio components

    /// Metadata returned when receiving packets.
    /// Contains signal quality information typical of radio systems.
    #[derive(Debug, Clone, PartialEq)]
    struct RadioInfo {
        /// Received Signal Strength Indicator in dBm
        rssi: i16,
        /// Link Quality Indicator (0-255, higher is better)
        lqi: u8,
    }

    /// Radio states that can be set and queried.
    /// These represent typical operating modes of a radio chip.
    #[derive(Debug, Clone, PartialEq)]
    enum RadioState {
        /// Radio is idle, ready to transmit or receive
        Idle,
        /// Radio is actively transmitting
        Transmitting,
        /// Radio is in receive mode, listening for packets
        Receiving,
        /// Radio is in low-power sleep mode
        Sleep,
    }

    /// Errors that can occur during radio operations.
    #[derive(Debug, Clone, PartialEq)]
    enum RadioError {
        /// Operation timed out
        Timeout,
        /// Channel is busy (Clear Channel Assessment failed)
        ChannelBusy,
        /// Packet too large for radio buffer
        PacketTooLarge,
        /// Radio hardware error
        HardwareFault,
    }

    /// Delay implementation for tokio runtime.
    /// In embedded systems, the platform's delay (e.g., Embassy's Timer) should be used instead.
    #[derive(Debug, Clone, Copy, Default)]
    struct TokioDelay;

    impl DelayNs for TokioDelay {
        async fn delay_ns(&mut self, ns: u32) {
            tokio::time::sleep(core::time::Duration::from_nanos(ns as u64)).await;
        }
    }

    type RadioMock = Mock<RadioInfo, RadioState, RadioError, TokioDelay>;
    type RadioTransaction = Transaction<RadioInfo, RadioState, RadioError>;

    #[tokio::test]
    async fn basic_transmit() {
        // Create a mock that expects one transmit operation with specific data
        let mut radio = RadioMock::new(&[
            RadioTransaction::transmit(&[0xAA, 0xBB, 0xCC])
        ]);

        // Perform the transmit operation - this will be verified against expectations
        radio.transmit(&[0xAA, 0xBB, 0xCC]).await.unwrap();

        // Verify all expected transactions were completed
        radio.done();
    }

    /// Simulate various error conditions
    #[tokio::test]
    async fn simulating_errors() {
        // Create a mock with various error scenarios
        let mut radio = RadioMock::new(&[
            // Channel busy error (e.g., another device transmitting)
            RadioTransaction::transmit(&[0xAA, 0xBB])
                .with_error(RadioError::ChannelBusy),

            // Timeout error (e.g., no acknowledgment received)
            RadioTransaction::transmit(&[0xCC, 0xDD])
                .with_error(RadioError::Timeout),

            // Packet too large for radio buffer
            RadioTransaction::transmit(&[0xEE, 0xFF])
                .with_error(RadioError::PacketTooLarge),

            // Hardware fault detected
            RadioTransaction::set_power(Dbm(20))
                .with_error(RadioError::HardwareFault),
        ]);

        // Test channel busy error
        let result = radio.transmit(&[0xAA, 0xBB]).await;
        assert_eq!(result, Err(RadioError::ChannelBusy));

        // Test timeout error
        let result = radio.transmit(&[0xCC, 0xDD]).await;
        assert_eq!(result, Err(RadioError::Timeout));

        // Test packet too large error
        let result = radio.transmit(&[0xEE, 0xFF]).await;
        assert_eq!(result, Err(RadioError::PacketTooLarge));

        // Test hardware fault
        let result = radio.set_power(Dbm(20)).await;
        assert_eq!(result, Err(RadioError::HardwareFault));

        radio.done();
    }

    /// Mock validates data matches expectations
    #[tokio::test]
    #[should_panic(expected = "Data mismatch")]
    async fn validation_wrong_data() {
        let mut radio = RadioMock::new(&[
            RadioTransaction::transmit(&[0xAA, 0xBB])  // Expecting this...
        ]);

        // But we transmit different data - this will panic!
        let _ = radio.transmit(&[0xCC, 0xDD]).await;
    }

    /// Receive data with signal quality metadata
    #[tokio::test(start_paused = true)]
    async fn receive_with_signal_info() {
        use core::time::Duration;
        use tokio::time::Instant;

        // Setup mock with realistic timing:
        // - listen() waits for packet detection (slow)
        // - receive() just reads the buffer (fast)
        let mut radio = RadioMock::new(&[
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(3)),  // Waiting for sync word detection
            RadioTransaction::receive(
                &[0xDE, 0xAD, 0xBE, 0xEF],
                RadioInfo {
                    rssi: -65,
                    lqi: 240
                },
            )
            .with_delay(Duration::from_millis(10)),  // Quick buffer read
        ]);

        // Start listening for packets (this takes time)
        let listen_start = Instant::now();
        radio.listen().await.unwrap();
        assert!(listen_start.elapsed() >= Duration::from_secs(3));

        // Receive the packet (this is fast)
        let receive_start = Instant::now();
        let mut buffer = [0u8; 32];
        let (bytes_received, info) = radio.receive(&mut buffer).await.unwrap();
        assert!(receive_start.elapsed() < Duration::from_millis(50));

        // Verify the received data and metadata
        assert_eq!(bytes_received, 4);
        assert_eq!(&buffer[..4], &[0xDE, 0xAD, 0xBE, 0xEF]);
        assert_eq!(info.rssi, -65);
        assert_eq!(info.lqi, 240);

        radio.done();
    }

    /// Configure transmission power levels
    #[tokio::test]
    async fn power_configuration() {
        let mut radio = RadioMock::new(&[
            // Set to low power for close-range communication
            RadioTransaction::set_power(Dbm(0)),
            // Later increase for long-range
            RadioTransaction::set_power(Dbm(20)),
        ]);

        // Configure for short range
        radio.set_power(Dbm(0)).await.unwrap();

        // Later, boost for long range
        radio.set_power(Dbm(20)).await.unwrap();

        radio.done();
    }

    /// Test all radio state transitions
    #[tokio::test]
    async fn state_transitions() {
        let mut radio = RadioMock::new(&[
            // Start in idle state
            RadioTransaction::get_state(RadioState::Idle),

            // Transition to transmit mode
            RadioTransaction::set_state(RadioState::Transmitting),
            RadioTransaction::get_state(RadioState::Transmitting),

            // Back to idle after transmit
            RadioTransaction::set_state(RadioState::Idle),

            // Switch to receive mode
            RadioTransaction::set_state(RadioState::Receiving),
            RadioTransaction::get_state(RadioState::Receiving),

            // Back to idle
            RadioTransaction::set_state(RadioState::Idle),

            // Enter sleep mode for power saving
            RadioTransaction::set_state(RadioState::Sleep),
            RadioTransaction::get_state(RadioState::Sleep),

            // Wake up to idle
            RadioTransaction::set_state(RadioState::Idle),
        ]);

        // Verify initial state
        let state = radio.get_state().await.unwrap();
        assert_eq!(state, RadioState::Idle);

        // Transmit mode
        radio.set_state(RadioState::Transmitting).await.unwrap();
        assert_eq!(radio.get_state().await.unwrap(), RadioState::Transmitting);

        // Back to idle
        radio.set_state(RadioState::Idle).await.unwrap();

        // Receive mode
        radio.set_state(RadioState::Receiving).await.unwrap();
        assert_eq!(radio.get_state().await.unwrap(), RadioState::Receiving);

        // Back to idle
        radio.set_state(RadioState::Idle).await.unwrap();

        // Sleep mode for power saving
        radio.set_state(RadioState::Sleep).await.unwrap();
        assert_eq!(radio.get_state().await.unwrap(), RadioState::Sleep);

        // Wake up
        radio.set_state(RadioState::Idle).await.unwrap();

        radio.done();
    }

    /// Complete transmit/receive workflow
    #[tokio::test(start_paused = true)]
    async fn complete_workflow() {
        use core::time::Duration;

        // Define expected sequence with realistic timing
        let mut radio = RadioMock::new(&[
            // 1. Configure transmission power (fast)
            RadioTransaction::set_power(Dbm(15)),
            // 2. Send a command packet (moderate speed)
            RadioTransaction::transmit(&[0x01, 0xC0, 0xFF, 0xEE])
                .with_delay(Duration::from_millis(50)),
            // 3. Wait for response (slow - waiting for sync word)
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(2)),
            // 4. Read the detected packet (fast)
            RadioTransaction::receive(
                &[0xAC, 0xCE],  // ACK packet
                RadioInfo { rssi: -45, lqi: 200 },
            )
            .with_delay(Duration::from_millis(5)),
        ]);

        // Execute the workflow
        radio.set_power(Dbm(15)).await.unwrap();
        radio.transmit(&[0x01, 0xC0, 0xFF, 0xEE]).await.unwrap();
        radio.listen().await.unwrap();  // This is where we wait

        let mut buffer = [0u8; 10];
        let (len, info) = radio.receive(&mut buffer).await.unwrap();  // This is quick

        // Verify acknowledgment received
        assert_eq!(len, 2);
        assert_eq!(&buffer[..2], &[0xAC, 0xCE]);
        assert_eq!(info.rssi, -45);

        radio.done();
    }

    /// Operations with simulated hardware timing
    #[tokio::test(start_paused = true)]
    async fn operations_with_delays() {
        use core::time::Duration;
        use tokio::time::Instant;

        let mut radio = RadioMock::new(&[
            // Radio configuration is relatively fast
            RadioTransaction::set_power(Dbm(10))
                .with_delay(Duration::from_millis(50)),

            // Listen waits for packet detection (slow)
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(4)),

            // Receive just reads the buffer (fast)
            RadioTransaction::receive(
                &[0xAB, 0xCD],
                RadioInfo { rssi: -70, lqi: 180 },
            ).with_delay(Duration::from_millis(10)),
        ]);

        // Measure power setting time
        let start = Instant::now();
        radio.set_power(Dbm(10)).await.unwrap();
        let power_time = start.elapsed();
        assert!(power_time >= Duration::from_millis(50));

        // Listen takes time (waiting for sync word)
        let start = Instant::now();
        radio.listen().await.unwrap();
        let listen_time = start.elapsed();
        assert!(listen_time >= Duration::from_secs(4));

        // Receive is fast (just reading buffer)
        let start = Instant::now();
        let mut buffer = [0u8; 10];
        let _ = radio.receive(&mut buffer).await.unwrap();
        let receive_time = start.elapsed();
        assert!(receive_time < Duration::from_millis(50));

        radio.done();
    }

    /// Verify all transactions must be consumed
    #[tokio::test]
    #[should_panic(expected = "Not all transactions were consumed")]
    async fn incomplete_transactions_panic() {
        let mut radio = RadioMock::new(&[
            RadioTransaction::transmit(&[0xAA]),
            RadioTransaction::transmit(&[0xBB]),  // This won't be consumed
        ]);

        // We only do one transmit but expect two
        radio.transmit(&[0xAA]).await.unwrap();

        // This will panic because we didn't consume all transactions
        radio.done();
    }

    /// Operations must match expected order
    #[tokio::test]
    #[should_panic(expected = "Expected Transmit transaction")]
    async fn wrong_operation_order() {
        let mut radio = RadioMock::new(&[
            RadioTransaction::listen(),  // Expecting listen first...
        ]);

        // But we transmit instead - this will panic!
        let _ = radio.transmit(&[0xAA]).await;
    }

    /// Unexpected operations panic
    #[tokio::test]
    #[should_panic(expected = "no expectation for")]
    async fn unexpected_operation() {
        let mut radio = RadioMock::new(&[
            // Empty expectations
        ]);

        // Any operation will panic since nothing is expected
        let _ = radio.transmit(&[0xAA]).await;
    }

    /// Test timeout and retry pattern
    #[tokio::test(start_paused = true)]
    async fn timeout_handling() {
        use core::time::Duration;
        use tokio::time::{timeout, Instant};

        // Realistic pattern: listen (slow) -> receive (timeout) -> listen again -> receive
        let mut radio = RadioMock::new(&[
            // First attempt: packet arrives late
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(2)),  // Waiting for sync word
            RadioTransaction::receive(
                &[0xCC, 0xDD],
                RadioInfo { rssi: -50, lqi: 100 },
            )
            .with_delay(Duration::from_secs(2)), // Packet corrupted, takes too long

            // After timeout, we listen again
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(1)),  // Packet arrives sooner
            RadioTransaction::receive(
                &[0xEE, 0xFF],
                RadioInfo { rssi: -60, lqi: 90 },
            )
            .with_delay(Duration::from_millis(10)),  // Quick successful read
        ]);

        // First attempt
        radio.listen().await.unwrap();

        // Try to receive with 1-second timeout (will fail)
        let start = Instant::now();
        let mut buffer = [0u8; 10];
        let result = timeout(Duration::from_secs(1), radio.receive(&mut buffer)).await;

        // Should timeout because receive takes 2 seconds
        assert!(result.is_err(), "Should timeout after 1 second");
        assert!(start.elapsed() >= Duration::from_secs(1));

        // Retry: listen again then receive
        radio.listen().await.unwrap();
        let (len, _info) = radio.receive(&mut buffer).await.unwrap();
        assert_eq!(len, 2);
        assert_eq!(&buffer[..2], &[0xEE, 0xFF]);

        radio.done();
    }

    /// Demonstrate waiting pattern with select!
    #[tokio::test(start_paused = true)]
    async fn select_with_timeout() {
        use core::time::Duration;
        use tokio::select;
        use tokio::time::sleep;

        // Create a simple delay transaction to show select! usage
        // Note: Due to mock implementation details, the delay happens
        // inside the operation and doesn't properly interact with select!
        // This test demonstrates the pattern even if timing isn't perfect
        let mut radio = RadioMock::new(&[
            RadioTransaction::listen()
                .with_delay(Duration::from_millis(100)),
        ]);

        // Example of how select! would be used in real code
        let result = select! {
            res = radio.listen() => {
                res.unwrap();
                "packet_detected"
            }
            _ = sleep(Duration::from_secs(10)) => {
                "timeout"
            }
        };

        // In this test, listen completes because mock delays are internal
        // In real radio drivers, the future would properly pend
        assert_eq!(result, "packet_detected");

        // This demonstrates the pattern even if mock timing differs from real hardware
    }

    /// Operation completes before timeout
    #[tokio::test(start_paused = true)]
    async fn operation_completes_before_timeout() {
        use core::time::Duration;
        use tokio::select;
        use tokio::time::{sleep, Instant};

        let mut radio = RadioMock::new(&[
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(1)), // Packet arrives quickly
            RadioTransaction::receive(
                &[0xAA, 0xBB],
                RadioInfo { rssi: -40, lqi: 90 },
            )
            .with_delay(Duration::from_millis(10)), // Fast buffer read
        ]);

        let start = Instant::now();

        // Race: listen (1 second) vs timeout (3 seconds)
        let result = select! {
            res = radio.listen() => {
                res.unwrap();
                // Now quickly read the packet
                let mut buffer = [0u8; 10];
                let (len, info) = radio.receive(&mut buffer).await.unwrap();
                assert_eq!(len, 2);
                assert_eq!(&buffer[..2], &[0xAA, 0xBB]);
                assert_eq!(info.rssi, -40);
                "received"
            }
            _ = sleep(Duration::from_secs(3)) => {
                "timeout"
            }
        };

        // Listen and receive should complete first
        assert_eq!(result, "received");
        assert!(start.elapsed() >= Duration::from_secs(1));
        assert!(start.elapsed() < Duration::from_secs(2));

        radio.done();  // All transactions completed successfully
    }

    /// Retry pattern after receive timeout
    #[tokio::test(start_paused = true)]
    async fn retry_after_receive_timeout() {
        use core::time::Duration;
        use tokio::time::timeout;

        // Pattern: listen -> receive (corrupted/timeout) -> listen -> receive (success)
        let mut radio = RadioMock::new(&[
            // First attempt
            RadioTransaction::listen()
                .with_delay(Duration::from_millis(500)), // Quick detection
            RadioTransaction::receive(
                &[0x00, 0x00],  // Corrupted packet
                RadioInfo { rssi: -90, lqi: 30 },
            )
            .with_delay(Duration::from_secs(5)), // CRC error, times out

            // Retry after timeout
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(2)), // Wait for clean packet
            RadioTransaction::receive(
                &[0xAA, 0xBB],  // Good packet
                RadioInfo { rssi: -50, lqi: 200 },
            )
            .with_delay(Duration::from_millis(5)), // Quick read
        ]);

        // First attempt - packet detected quickly
        radio.listen().await.unwrap();

        // Try to receive but it times out (corrupted packet)
        let mut buffer = [0u8; 10];
        let result = timeout(
            Duration::from_millis(100),
            radio.receive(&mut buffer)
        ).await;
        assert!(result.is_err(), "Should timeout on corrupted packet");

        // Proper retry pattern: listen again then receive
        radio.listen().await.unwrap();
        let (len, info) = radio.receive(&mut buffer).await.unwrap();

        assert_eq!(len, 2);
        assert_eq!(&buffer[..2], &[0xAA, 0xBB]);
        assert_eq!(info.rssi, -50);
        assert_eq!(info.lqi, 200);

        radio.done();
    }

    /// Complex sequence with mixed timing requirements
    #[tokio::test(start_paused = true)]
    async fn mixed_timing_operations() {
        use core::time::Duration;
        use tokio::time::Instant;

        let mut radio = RadioMock::new(&[
            // Power configuration is fast
            RadioTransaction::set_power(Dbm(10)),

            // Transmit packet (moderate speed)
            RadioTransaction::transmit(&[0x01, 0x02])
                .with_delay(Duration::from_millis(30)),

            // Wait for response (slow - waiting for sync word)
            RadioTransaction::listen()
                .with_delay(Duration::from_secs(3)),

            // Read received packet (fast)
            RadioTransaction::receive(
                &[0x03, 0x04],
                RadioInfo { rssi: -55, lqi: 185 },
            )
            .with_delay(Duration::from_millis(5)),

            // Send ACK quickly
            RadioTransaction::transmit(&[0xAC, 0xDC])
                .with_delay(Duration::from_millis(10)),
        ]);

        // Execute sequence with timing verification
        let start = Instant::now();

        // Fast configuration
        radio.set_power(Dbm(10)).await.unwrap();
        assert!(start.elapsed() < Duration::from_millis(5));

        // Transmit with moderate delay
        let tx_start = Instant::now();
        radio.transmit(&[0x01, 0x02]).await.unwrap();
        assert!(tx_start.elapsed() >= Duration::from_millis(30));

        // Listen for response (this is where we wait)
        let listen_start = Instant::now();
        radio.listen().await.unwrap();
        assert!(listen_start.elapsed() >= Duration::from_secs(3));

        // Receive is quick
        let receive_start = Instant::now();
        let mut buffer = [0u8; 10];
        let (len, _info) = radio.receive(&mut buffer).await.unwrap();
        assert!(receive_start.elapsed() < Duration::from_millis(50));
        assert_eq!(&buffer[..len], &[0x03, 0x04]);

        // Send ACK
        let ack_start = Instant::now();
        radio.transmit(&[0xAC, 0xDC]).await.unwrap();
        assert!(ack_start.elapsed() >= Duration::from_millis(10));

        radio.done();
    }
}