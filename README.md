# json-escape

[![crates.io](https://img.shields.io/crates/v/json-escape.svg)](https://crates.io/crates/json-escape)
[![docs.rs](https://docs.rs/json-escape/badge.svg)](https://docs.rs/json-escape)
[![CI](https://github.com/veecore/json-escape/actions/workflows/ci.yml/badge.svg)](https://github.com/veecore/json-escape/actions)

A highly **ergonomic**, well-tested, `no_std` library for streaming JSON string escaping and unescaping. It processes JSON strings with **zero-copy slicing** and **no intermediate allocations**, ensuring both high performance and **RFC-compliant** correctness, ideal for parsers, I/O operations, and memory-constrained environments. ✅

The core of the library is two **iterator-based structs** that enable its streaming nature:

  - **`Escape`**: Lazily yields escaped string slices from an input `&str`.
  - **`Unescape`**: Lazily yields unescaped byte slices from an input `&[u8]`.

This streaming approach avoids allocating a single large `String` or `Vec<u8>` for the result, making it incredibly efficient for large data processing.

-----

## Key Features

  - **🎯 Ergonomic & Intuitive**: Simple-to-use functions like `escape_str` and `unescape` return familiar iterators that integrate cleanly with Rust's ecosystem.
  - **🚀 Streaming & Iterator-based**: Process data in chunks without buffering the entire result in memory, delivering high performance for large payloads.
  - **✨ Zero-Copy Slicing**: For sequences of characters that don't need modification, the iterators yield slices borrowed directly from the input.
  - **✅ Correct & Compliant**: Fully compliant with the JSON RFC for all escape sequences, including full support for UTF-16 surrogate pairs (`\uD83D\uDE00` for 😀).
  - **🧩 `no_std` Compatible**: Usable in embedded systems and other memory-constrained environments (with the `alloc` feature for owned conversions).
  - **⚙️ Full Functionality**: Implements `PartialEq` for convenient testing and provides `std::io::Read` integration (with the `std` feature) for plugging directly into libraries like `serde_json`.

-----

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
```

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

## Performance

The library's design focuses on minimizing allocations, leading to superior performance, especially when dealing with large payloads or zero-copy streaming.

Benchmarks confirm that `json-escape` is significantly faster than standard methods when avoiding unnecessary allocations.

| Operation | Scenario | `json-escape` (Median Time) | Comparison (e.g., `serde_json` or Main API) |
| :--- | :--- | :--- | :--- |
| **Escaping** (Collect to String) | No Escapes | **$309.95\\text{ ns}$ (Explicit API)** | $338.38\\text{ ns}$ (Main API) |
| **Unescaping** (Iterate Only) | No Escapes | **$54.999\\text{ ns}$ (Explicit API)** | $88.443\\text{ ns}$ (Main API) |
| **Escaping** (Iterate Only) | Dense Escapes | **$236.56\\text{ ns}$ (Explicit API)** | $278.02\\text{ ns}$ (Main API) |
| **Unescaping** (Iterate Only) | Dense Escapes | **$200.87\\text{ ns}$ (Explicit API)** | $501.67\\text{ ns}$ (Main API) |
| **Unescaping** (Decode UTF-8) | Unicode | **$1.5011\\text{ ms}$ (Explicit API)** | $1.8918\\text{ ms}$ (Main API) |
| **Escaping to String** | Sparse Escapes | **\~2.8% to \~8.8% Faster** | `serde_json::to_string` |
| **Unescaping from Str** | No Escapes | **\~2.8% Faster** | `serde_json::from_str` |

### Key Takeaways

1.  **Zero-Allocation Wins**: For I/O-bound tasks using the `Write to Sink` or `std::io::Read` integrations, both the `Main` and `Explicit` APIs show near-identical, minimal overhead ($\<159\~\\text{ps}$), which is the most efficient method for large data.
2.  **`Explicit` Module Advantage (Unescaping)**: The new `explicit` module significantly outperforms the main API in **unescaping** when used for pure iteration or in dense/sparse escape scenarios, sometimes being **over 2x faster** (e.g., Sparse or Dense Escapes). This is likely due to the structural clarity of its chunks simplifying internal logic.
3.  **Overall Speed**: `json-escape` consistently outperforms the overhead of allocating and parsing with general-purpose tools like `serde_json` for simple string conversion tasks.

-----

## Fine-Grained Control with the `explicit` Module

The new `json_escape::explicit` module provides **more detail and control** by yielding chunk structs that explicitly separate the literal text from the escaped/unescaped character. This is useful for advanced debugging, logging, and custom stream processing.

### Explicit Escaping

The `Escape` iterator in this module yields an `EscapedChunk<'a>` containing the `literal()` slice and the `escaped()` static string.

```rust
use json_escape::explicit::escape_str;

let mut escaper = escape_str("a\nb");

let chunk1 = escaper.next().unwrap();
assert_eq!("a", chunk1.literal());
assert_eq!(Some(r#"\n"#), chunk1.escaped());

let chunk2 = escaper.next().unwrap();
assert_eq!("b", chunk2.literal());
assert_eq!(None, chunk2.escaped());
```

### Explicit Unescaping

The `Unescape` iterator yields an `UnescapedChunk<'a>` containing the `literal()` byte slice and the `unescaped()` character.

```rust
use json_escape::explicit::unescape;

let mut unescaper = unescape(br"hello\tworld");

let chunk1 = unescaper.next().unwrap().unwrap();
assert_eq!(b"hello", chunk1.literal());
assert_eq!(Some('\t'), chunk1.unescaped());

let chunk2 = unescaper.next().unwrap().unwrap();
assert_eq!(b"world", chunk2.literal());
assert_eq!(None, chunk2.unescaped());
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

`json-escape` avoids the standard inefficient practice of allocating a new `String` for the unescaped `payload` by plugging its streaming `Unescape` reader directly into `serde_json`.

### The `json-escape` Solution: No Intermediate Allocation\!

```rust
use json_escape::unescape_quoted; // Use the crate root function
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
    // NOTE: unescape_quoted is available in both the root and 'explicit' module.
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
json-escape = "0.1.2"
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

  - Apache License, Version 2.0, ([LICENSE-APACHE](http://www.apache.org/licenses/LICENSE-2.0))
  - MIT license ([LICENSE-MIT](http://opensource.org/licenses/MIT))

at your option.