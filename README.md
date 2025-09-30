# json-escape

[![crates.io](https://img.shields.io/crates/v/json-escape.svg)](https://crates.io/crates/json-escape)
[![docs.rs](https://docs.rs/json-escape/badge.svg)](https://docs.rs/json-escape)
[![CI](https://github.com/veecore/json-escape/actions/workflows/ci.yml/badge.svg)](https://github.com/veecore/json-escape/actions)

A highly **ergonomic**, well-tested, `no_std` library for streaming JSON string escaping and unescaping. It processes JSON strings with **zero-copy slicing** and **no intermediate allocations**, ensuring both high performance and **RFC-compliant** correctness, ideal for parsers, I/O operations, and memory-constrained environments. ✅

The library provides a layered API to fit your needs:

- **High-Level Iterators**: The `escape_str` and `unescape` functions provide a simple, iterator-based way to process entire string slices.
- **Streaming for I/O**: The `stream::UnescapeStream` struct processes data in chunks, perfect for reading from files or network sockets.
- **Low-Level Tokens**: The `token` module offers the most granular control for building custom processors.

This multi-faceted approach avoids allocating a single large buffer for the result, making it incredibly efficient for large data processing.

---

## Key Features

- **🎯 Ergonomic & Intuitive**: Simple-to-use functions that integrate cleanly with Rust's ecosystem.
- **🚀 True Streaming for I/O**: The `stream` module handles chunked data from any source, correctly parsing escape sequences that are split across buffer boundaries.
- **✨ Zero-Copy Slicing**: For sequences that don't need modification, the iterators yield slices borrowed directly from the input.
- **✅ Correct & Compliant**: Fully compliant with RFC 8259 for all escape sequences, including full support for UTF-16 surrogate pairs (`\uD83D\uDE00` for 😀).
- **🧩 `no_std` Compatible**: Usable in embedded systems and other memory-constrained environments (with the `alloc` feature for owned conversions).
- **⚙️ Full Functionality**: Implements `PartialEq` for convenient testing and provides `std::io::Read` integration (with the `std` feature) for plugging directly into libraries like `serde_json`.

---

## Quick Start

### Escaping a String

```rust
use json_escape::escape_str;
use std::borrow::Cow;

let input = "Hello, \"world\"!\nThis is a backslash: \\";
let expected = r#"Hello, \"world\"!\nThis is a backslash: \\"#;

// escape_str returns an iterator. Collect it into a String.
let escaped_string: String = escape_str(input).collect();
assert_eq!(escaped_string, expected);
````

### Unescaping a String Slice

```rust
use json_escape::unescape;
use std::borrow::Cow;

let input = r#"Emoji: \uD83D\uDE00 and a tab\t!"#;
let expected = "Emoji: 😀 and a tab\t!";

// unescape returns an iterator over Result<&[u8], _>.
// The `decode_utf8` helper collects and validates the output.
let decoded_cow: Cow<str> = unescape(input).decode_utf8().unwrap();
assert_eq!(decoded_cow, expected);
```

-----

## Streaming Unescape for I/O 🚀

The most powerful feature is the ability to unescape a stream of data chunks without buffering them. The `stream::UnescapeStream` struct is designed for this purpose.

You "push" byte slices into the unescaper as you receive them (e.g., from a file or network socket). It correctly handles complex escape sequences, like surrogate pairs, that might be split across chunks.

```rust
use json_escape::{stream::UnescapeStream, token::UnescapedToken};

// A JSON string split into multiple parts.
// The surrogate pair `\uD83D\uDE00` (😀) is split across the boundary.
let parts = vec![
    br#"Hello, W\"orld! \uD83D"#.as_slice(),
    br#"\uDE00 Goodbye!"#.as_slice(),
];

let mut unescaper = UnescapeStream::new();
let mut unescaped_string = String::new();

for part in parts {
    // Process the next part of the stream.
    // This yields any character that was completed at the boundary plus an
    // iterator for the rest of the chunk.
    let (boundary_char, rest_of_part) = unescaper.try_unescape_next(part).unwrap();

    // 1. Handle the character that may have spanned the boundary.
    if let Some(c) = boundary_char {
        unescaped_string.push(c);
    }

    // 2. Process the rest of the current chunk.
    for token in rest_of_part {
        match token.unwrap() {
            UnescapedToken::Literal(literal) => {
                unescaped_string.push_str(std::str::from_utf8(literal).unwrap())
            }
            UnescapedToken::Unescaped(ch) => unescaped_string.push(ch),
        }
    }
}

// IMPORTANT: Always call finish() to detect errors at the end of the stream.
unescaper.finish().unwrap();

assert_eq!(unescaped_string, r#"Hello, W"orld! 😀 Goodbye!"#);
println!("Successfully unescaped stream: {}", unescaped_string);
```

-----

## Performance

The library's design focuses on minimizing allocations and maximizing throughput. The new SWAR-based (SIMD Within a Register) escape detection algorithm makes scanning for escapes nearly free.

| Operation | Scenario | `json-escape` Performance |
| :--- | :--- | :--- |
| **Unescaping** | No Escapes | **\~2.5× faster** than byte-by-byte scan |
| **Unescaping** | Sparse Escapes | **\~1.8× faster** than byte-by-byte scan |
| **Unescaping** | Dense Unicode | **\~2.2× faster** than byte-by-byte scan |
| **Escaping to String** | Sparse Escapes | **Consistently Faster** than `serde_json::to_string` |
| **Unescaping from Str** | No Escapes | **Consistently Faster** than `serde_json::from_str` |

For I/O-bound tasks using `Write to Sink` or `std::io::Read` integrations, the overhead is negligible, making it the most efficient method for large data.

-----

## Low-Level APIs (`token` and `explicit`)

For advanced use cases, the `token` and `explicit` modules provide more granular control.

  - `json_escape::token`: The lowest-level API. It yields `UnescapedToken` and `EscapedToken` enums, which separate literal slices from processed characters. This is the most flexible and composable API, ideal for building custom state machines or processors.
  - `json_escape::explicit`: A slightly higher-level API that yields chunk structs (`UnescapedChunk`, `EscapedChunk`). These structs provide methods to inspect literal and processed parts, which is useful for debugging and logging.

-----

## Examples

You can find complete, runnable examples in the `examples/` directory of the project repository. These are great for copy-pasting and learning how to use the library in different scenarios:

  - `simple_unescape.rs`: Basic usage of the high-level `unescape` iterator.
  - `stream_file.rs`: A practical example of using `UnescapeStream` to read and process a file.
  - `zero_copy_serde.rs`: Demonstrates how to parse a JSON field containing an escaped JSON string directly into a `serde` struct without intermediate allocations.

-----

## Changelog

This project follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). All notable changes, including new features, bug fixes, and performance improvements, are documented in the **[`CHANGELOG.md`](CHANGELOG.md)** file. We encourage users to review it for transparency between releases.

-----

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
json-escape = "0.3.0"
```

### Feature Flags

  - `alloc` (enabled by default): Provides `Cow`, `String`, and `Vec` conversions.
  - `std` (enabled by default): Provides `std::io::Read` and `std::error::Error` implementations.

For `no_std` environments without an allocator, use:

```toml
[dependencies]
json-escape = { version = "0.3.0", default-features = false }
```

## License

This project is licensed under either of

  - Apache License, Version 2.0, ([LICENSE-APACHE](http://www.apache.org/licenses/LICENSE-2.0))
  - MIT license ([LICENSE-MIT](http://opensource.org/licenses/MIT))

at your option.