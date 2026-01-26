# embedded-radio-async

Async-native traits for packet radio devices, designed for embedded systems.

This crate aims to provide minimal, flexible trait abstractions for packet radio devices with async operations built-in from the ground up. While the existing [radio](https://crates.io/crates/radio) crate offers blocking traits with async wrappers that poll for completion, this crate takes a different approach by leveraging native async capabilities of runtimes like [Embassy](https://embassy.dev/). This enables implementations to use interrupt-driven or event-based patterns that can be more efficient for resource-constrained embedded devices while still allowing implementations to use polling if desired.

## Features

- **Async-native design**: All operations are inherently async, not wrappers around blocking code
- **Minimal and flexible**: Traits provide only essential operations, maximizing implementation freedom
- **`no_std` by design**: Built for embedded environments from the ground up

## Testing

The `mock` feature provides a `no_std`-compatible, transaction-based mock implementation for testing code that depends on radio traits. Following patterns similar to `embedded-hal-mock`, the mock works on both host test environments and embedded targets, enabling comprehensive testing across platforms. It supports:

- **Transaction verification**: Define expected operations and their responses upfront
- **Configurable delays**: Simulate realistic hardware timing behavior for operations
- **Timeout testing**: Use delays with `select!` and timeout patterns to test race conditions and async behavior
- **Error injection**: Simulate various error scenarios (timeouts, channel busy, hardware faults, etc.)
- **Generic over types**: Works with custom Info, State, Error, and Delay types

Enable the mock with the `mock` feature flag in your `Cargo.toml`

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE.md) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT.md) or <http://opensource.org/licenses/MIT>)

at your option.

## Contributing

Contributions are welcome! This crate aims to provide minimal, flexible abstractions. When proposing changes:

- Prefer flexibility over specificity
- Consider diverse radio architectures (sub-GHz, 2.4GHz, LoRa, FSK, etc.)
- Maintain `no_std` compatibility
- Document design rationale in proposals

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.