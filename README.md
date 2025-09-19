# json-escape

[![crates.io](https://img.shields.io/crates/v/json-escape.svg)](https://crates.io/crates/json-escape)
[![docs.rs](https://docs.rs/json-escape/badge.svg)](https://docs.rs/json-escape)
[![CI](https://github.com/veecore/json-escape/actions/workflows/ci.yml/badge.svg)](https://github.com/veecore/json-escape/actions)

A high-performance, `no_std` compatible library for streaming JSON string escaping and unescaping. Process large JSON strings with zero-copy slicing and no intermediate allocations, ideal for parsers and memory-constrained environments. ⚡

The core of the library is two iterator-based structs:
- **`Escape`**: Lazily yields escaped string slices from an input `&str`.
- **`Unescape`**: Lazily yields unescaped byte slices from an input `&[u8]`.

This streaming approach avoids allocating a single large `String` for the result, making it incredibly efficient for large data and I/O operations.

---

## Key Features

- **🚀 Streaming & Iterator-based**: Process data in chunks without buffering the entire result in memory.
- **✨ Zero-Copy Slicing**: For sequences of characters that don't need modification, the iterators yield slices borrowed directly from the input.
- **🧩 `no_std` Compatible**: Usable in embedded systems and other memory-constrained environments (with `alloc` for owned conversions).
- **Unicode Excellence**: Correctly decodes `\uXXXX` sequences, including full support for UTF-16 surrogate pairs (e.g., `\uD83D\uDE00` for 😀).
- **🔎 Robust Error Handling**: The `Unescape` iterator returns descriptive errors for invalid or truncated escape sequences.
- **`std::io` Integration**: With the `std` feature, `Unescape` implements `std::io::Read`, allowing it to be plugged directly into APIs that consume readers (like `serde_json`).

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

// For efficiency, convert to a Cow<str>. This avoids allocation
// if the input string requires no escaping.
let cow: Cow<str> = escape_str("no escapes needed").into();
assert!(matches!(cow, Cow::Borrowed(_)));
````

### Unescaping a String

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

## Advanced Usage: Zero-Allocation REST API Parsing

A common scenario in web services is receiving a JSON payload where one of the fields is *another* JSON object, escaped as a string.

```json
{
  "transaction_id": "txn_123",
  "payload": "{\"user_id\": 42, \"items\": [\"apple\", \"orange\"], \"metadata\": {\"source\": \"mobile\"}}"
}
```

The standard approach requires allocating a new `String` to hold the unescaped `payload` before parsing it. This is inefficient, especially for large payloads.

`json-escape` avoids this entirely by plugging its streaming `Unescape` reader directly into `serde_json`.

### The `json-escape` Solution: No Intermediate Allocation\!

```rust
use json_escape::unescape_quoted;
use serde::Deserialize;
use serde_json::RawValue;

// The inner payload we want to extract and parse.
#[derive(Deserialize, Debug)]
struct InnerPayload {
    user_id: u64,
    items: Vec<String>,
}

// The outer structure. We use `&RawValue` for a zero-copy view.
#[derive(Deserialize)]
struct OuterPayload<'a> {
    transaction_id: String,
    #[serde(borrow)]
    payload: &'a RawValue,
}

fn main() {
    let response_body = r#"{
        "transaction_id": "txn_123",
        "payload": "{\"user_id\": 42, \"items\": [\"apple\", \"orange\"]}"
    }"#;

    // 1. Parse the outer frame without allocating for `payload`.
    let outer: OuterPayload = serde_json::from_str(response_body).unwrap();

    // 2. Create a streaming reader from the raw, escaped payload.
    // This implements `std::io::Read`.
    let reader = unescape_quoted(outer.payload.get());

    // 3. Parse the inner payload directly from the reader.
    // NO intermediate `String` is ever allocated for the unescaped payload!
    let inner: InnerPayload = serde_json::from_reader(reader).unwrap();

    assert_eq!(inner.user_id, 42);
    assert_eq!(inner.items, vec!["apple", "orange"]);
    println!("Successfully parsed inner payload: {:?}", inner);
}
```

-----

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
json-escape = "0.1.1"
```

### Feature Flags

  - `alloc` (enabled by default): Provides `Cow`, `String`, and `Vec` conversions.
  - `std` (enabled by default): Provides `std::io::Read` and `std::error::Error` implementations.

For `no_std` environments without an allocator, use:

```toml
[dependencies]
json-escape = { version = "*", default-features = false }
```

## License

This project is licensed under either of

  - Apache License, Version 2.0, ([LICENSE-APACHE](https://www.google.com/search?q=LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
  - MIT license ([LICENSE-MIT](https://www.google.com/search?q=LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.