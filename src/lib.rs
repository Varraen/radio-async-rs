#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(async_fn_in_trait)]

#[cfg(feature = "mock")]
pub mod mock;

use core::fmt::Debug;

/// Radio trait combining the minimal required traits for a generic radio object.
///
/// This trait serves as a convenient bound for generic code that requires both
/// transmit and receive capabilities. Implementations automatically satisfy this
/// trait by implementing both [`Transmit`] and [`Receive`].
///
/// Additional capabilities such as [`Power`] control and [`State`] management
/// can be implemented separately as needed.
pub trait Radio: Transmit + Receive {}

/// Transmit capability for packet radio devices.
///
/// This trait provides the minimal interface for transmitting data packets. Implementations
/// are responsible for handling radio-specific details such as preamble, sync words, and
/// packet framing. Address filtering, if needed, can be embedded in the payload by the
/// caller or handled through implementation-specific configuration methods.
///
/// The trait is intentionally minimal to provide maximum flexibility for different radio
/// architectures and use cases.
pub trait Transmit {
    /// Radio error type.
    ///
    /// Implementations may use this to propagate underlying errors (e.g., SPI, I2C)
    /// or to describe radio-specific error conditions.
    type Error: Debug + 'static;

    /// Transmit a data packet.
    ///
    /// Sends the provided data and waits for transmission to complete. This method
    /// handles the complete transmit sequence including entering transmit mode,
    /// loading the data, and waiting for transmission completion.
    ///
    /// # Parameters
    ///
    /// * `data` - The packet data to transmit. The format and maximum length are
    ///   implementation-specific. Addressing information, if needed, can be
    ///   embedded in this payload.
    ///
    /// # Notes
    ///
    /// - Broadcast vs. unicast transmission is determined by the payload content
    ///   or radio configuration, not by this trait
    /// - Power level can be configured before calling this method via the [`Power`] trait
    /// - This method awaits transmission completion or an error occurrence
    async fn transmit(&mut self, data: &[u8]) -> Result<(), Self::Error>;
}

/// Receive capability for packet radio devices.
///
/// This trait provides a two-stage receive process: `listen()` to detect incoming packets,
/// and `receive()` to fetch the packet data. This separation allows applications to
/// interrupt the listening phase when needed while ensuring packet reception completes
/// atomically once started.
pub trait Receive {
    /// Radio error type.
    ///
    /// Implementations may use this to propagate underlying errors (e.g., SPI, I2C)
    /// or to describe radio-specific error conditions.
    type Error: Debug + 'static;

    /// Packet metadata provided with received packets.
    ///
    /// This type is implementation-specific and typically includes signal quality metrics.
    /// Recommended fields include:
    /// - **RSSI** (Received Signal Strength Indicator): Signal strength in dBm
    /// - **LQI** (Link Quality Indicator): Link quality metric (chip-specific scale)
    /// - **NRS** (Noise floor): Background noise level in dBm (if available)
    /// - **CRC Status**: Whether CRC validation passed (if applicable)
    ///
    /// The specific fields available depend on radio chip capabilities.
    type Info;

    /// Enter receive mode and wait for a valid packet to be detected.
    ///
    /// This method configures the radio for reception and waits until the sync word
    /// or preamble of an incoming packet is detected. The detection mechanism is
    /// implementation-specific and may use polling or interrupt-based detection.
    ///
    /// This method is designed to be interruptible (e.g., using `select!` in async code)
    /// to allow the application to handle other events while waiting for packets.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` when a valid packet preamble/sync word is detected and the
    /// radio is ready to receive. Call [`receive()`](Self::receive) immediately after
    /// to fetch the packet data.
    async fn listen(&mut self) -> Result<(), Self::Error>;

    /// Fetch a received packet.
    ///
    /// This method is intended to be called immediately after [`listen()`](Self::listen) returns
    /// successfully while the radio is in receive mode. It reads the packet data into
    /// the provided buffer and may wait for packet reception to complete.
    ///
    /// This is a critical section and interrupting it may result in packet loss or
    /// corruption.
    ///
    /// # Parameters
    ///
    /// * `buffer` - Buffer to store received packet data. The required size is
    ///   implementation-specific.
    ///
    /// # Returns
    ///
    /// Returns a tuple of:
    /// - The number of bytes received (written to `buffer`)
    /// - Metadata about the received packet (see [`Info`](Self::Info))
    async fn receive(&mut self, buffer: &mut [u8]) -> Result<(usize, Self::Info), Self::Error>;
}

/// Radio transmit power in dBm.
///
/// This type provides type safety for power values and allows implementations to
/// clip values to chip-specific valid ranges through custom `From` implementations
/// or conversion methods.
#[derive(Debug, Clone, PartialEq)]
pub struct Dbm(pub i8);

/// Power control for radio devices.
///
/// This trait provides transmit power configuration. Valid power ranges are
/// chip-specific and can be documented by implementations. The [`Dbm`] type
/// allows implementations to clip values to valid ranges.
pub trait Power {
    /// Radio error type.
    ///
    /// Implementations may use this to propagate underlying errors (e.g., SPI, I2C)
    /// or to describe radio-specific error conditions.
    type Error: Debug + 'static;

    /// Set the radio transmit power.
    ///
    /// Configures the output power for subsequent transmissions. The actual power
    /// range and granularity depend on the radio chip. Values outside the supported
    /// range can be clipped to the nearest valid value through the [`Dbm`] type.
    ///
    /// # Parameters
    ///
    /// * `power` - Transmit power in dBm. Implementations may document their
    ///   supported power range (e.g., -30 to +20 dBm for CC1200).
    ///
    /// # Notes
    ///
    /// - Power settings typically persist until explicitly changed
    /// - Some radios may have regulatory or hardware limitations on maximum power
    /// - Power changes may take effect immediately or on the next transmission,
    ///   depending on the implementation
    async fn set_power(&mut self, power: Dbm) -> Result<(), Self::Error>;
}

/// State management for radio devices.
///
/// This trait provides access to radio internal states. It is primarily intended for
/// use by radio driver implementations to manage state transitions. End users typically
/// do not need to call these methods directly, as higher-level methods (e.g., `transmit()`,
/// `listen()`) handle state transitions automatically.
///
/// Implementations can define states appropriate to their radio chip. Recommended
/// minimum states include:
/// - **Idle**: Radio is powered but not transmitting or receiving
/// - **Transmit**: Radio is transmitting a packet
/// - **Receive**: Radio is receiving or listening for packets
/// - **Sleep**: Radio is in low-power mode
///
/// Additional states may be defined for chip-specific modes (e.g., calibration,
/// frequency synthesis settling).
pub trait State {
    /// Radio error type.
    ///
    /// Implementations may use this to propagate underlying errors (e.g., SPI, I2C)
    /// or to describe radio-specific error conditions.
    type Error: Debug + 'static;

    /// Radio state type.
    ///
    /// This is implementation-specific and typically represented as an enum.
    /// See trait documentation for recommended minimum states.
    type State;

    /// Set the radio to a specific state.
    ///
    /// Commands the radio to transition to the specified state. This method is
    /// primarily for internal use by driver implementations.
    ///
    /// # Parameters
    ///
    /// * `state` - The desired radio state
    ///
    /// # Notes
    ///
    /// - State transitions may not be instantaneous
    /// - Invalid state transitions may return an error
    /// - End users typically do not need to call this method directly
    async fn set_state(&mut self, state: Self::State) -> Result<(), Self::Error>;

    /// Get the current radio state.
    ///
    /// Reads the current operating state from the radio. Useful for debugging,
    /// diagnostics, and error recovery.
    ///
    /// # Notes
    ///
    /// - The returned state reflects the radio's current condition at the time of the call
    /// - State may change asynchronously due to radio operations or external events
    async fn get_state(&mut self) -> Result<Self::State, Self::Error>;
}
