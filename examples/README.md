# json_escape Examples

This directory contains small, self-contained examples that demonstrate how to use
`json_escape` in different ways — from the simplest string unescape to advanced
streaming and zero-copy integration with `serde_json`.

Each example is runnable with:

```bash
cargo run --example <name>
````

---

## Examples

### 1. [`simple_unescape.rs`](simple_unescape.rs)

* **What it shows**: The basics of unescaping a string slice.
* **Key API**: [`unescape`] + `.decode_utf8()`
* **Run**:

  ```bash
  cargo run --example simple_unescape
  ```

---

### 2. [`stream_file.rs`](stream_file.rs)

* **What it shows**:
  Manual streaming unescape from a file using [`UnescapeStream`].
* **How it works**:

  * Reads a file in fixed-size chunks (`[u8; 8]` buffer).
  * Feeds each chunk into `try_unescape_next`.
  * Handles “boundary characters” and tokens manually.
* **Why it matters**:
  Teaches how streaming works under the hood and how to deal with chunked I/O.
* **Run**:

  ```bash
  cargo run --example stream_file
  ```

---

### 3. [`stream_file_fn.rs`](stream_file_fn.rs)

* **What it shows**:
  A higher-level version of the previous example using
  [`UnescapeStream::unescape_from_fn`].
* **How it works**:

  * `src` closure pulls chunks from the file.
  * `dst` closure consumes each [`UnescapedToken`].
  * `unescape_from_fn` drives the loop for you.
* **Why it matters**:
  Much simpler if you don’t need low-level control.
* **Run**:

  ```bash
  cargo run --example stream_file_fn
  ```

---

### 4. [`zero_copy_serde.rs`](zero_copy_serde.rs)

* **What it shows**:
  Advanced integration with [`serde_json`] using `RawValue`.
* **How it works**:

  * Parse outer JSON with a raw, escaped payload.
  * Use [`unescape_quoted`] to create a streaming reader.
  * Deserialize the inner payload directly without allocating an intermediate string.
* **Why it matters**:
  Demonstrates **zero-copy JSON parsing** for maximum efficiency.
* **Run**:

  ```bash
  cargo run --example zero_copy_serde
  ```

---

### 5. [`custom_processor_tokens.rs`](custom_processor_tokens.rs)

* **What it shows**:
  How to work directly with the low-level token API.
* **How it works**:

  * Iterate over [`EscapedToken`] when escaping.
  * Iterate over [`UnescapedToken`] when unescaping.
  * Custom processing logic (e.g. transforming or filtering tokens).
* **Why it matters**:
  Gives you maximum control if you need custom escape/unescape behavior.
* **Run**:

  ```bash
  cargo run --example custom_processor_tokens
  ```

---

## Suggested Learning Order

1. Start with **`simple_unescape.rs`** to understand the basics.
2. Move to **`stream_file.rs`** to see manual streaming.
3. Then try **`stream_file_fn.rs`** to learn the ergonomic driver.
4. Explore **`zero_copy_serde.rs`** for advanced serde integration.
5. Finally, dive into **`custom_processor_tokens.rs`** for low-level control.

---

## Key Types and Functions Used

* [`escape_str`] → Iterator of [`EscapedToken`].
* [`unescape`] → Iterator of [`UnescapedToken`] results.
* [`UnescapeStream`] → Incremental unescaper for chunked input.
* [`UnescapeStream::unescape_from_fn`] → Ergonomic streaming driver.
* [`unescape_quoted`] → Wraps a JSON string (with quotes + escapes) as a `Read` for `serde_json`.

---

## Running All Examples

```bash
cargo run --example simple_unescape
cargo run --example stream_file
cargo run --example stream_file_fn
cargo run --example zero_copy_serde
cargo run --example custom_processor_tokens
```

---

[serde_json]: https://docs.rs/serde_json
[`escape_str`]: ../src/token.rs
[`EscapedToken`]: ../src/token.rs
[`UnescapedToken`]: ../src/token.rs
[`unescape`]: ../src/token.rs
[`UnescapeStream`]: ../src/stream.rs
[`UnescapeStream::unescape_from_fn`]: ../src/stream.rs
[`unescape_quoted`]: ../src/lib.rs