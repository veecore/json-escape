use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use json_escape::stream::UnescapeStream;
use json_escape::token::UnescapedToken;
use json_escape::{escape_str, explicit, token, unescape, unescape_quoted};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::collections::HashMap;
use std::io::{self, Read, Write};

// --- Benchmark Data ---
// A string with no characters that need escaping to test the best-case scenario.
const NO_ESCAPES: &str = "This is a simple string without any special characters to escape. It's just plain ASCII text, designed to test the best-case performance scenario where the iterator can yield the entire string as a single slice without any processing.";
// A string with a few common escape sequences to represent a typical workload.
const SPARSE_ESCAPES: &str = r#"Here's a string with a "quote" and a \\ backslash.
It also includes a newline and a	tab. This represents a more typical use case for JSON strings."#;
// A string with many characters requiring escaping to stress-test the logic.
const DENSE_ESCAPES: &str = r#""\"\\\/\b\f\n\r\t""#;
// Raw and escaped versions of a string focused on Unicode escapes, including surrogate pairs.
const UNICODE_ESCAPES_RAW: &str = r#"Unicode test: éàçüö. Emoji: 😀. More symbols: ❤️✅."#;
const UNICODE_ESCAPES_ESCAPED: &str = r#"Unicode test: \u00e9\u00e0\u00e7\u00fc\u00f6. Emoji: \uD83D\uDE00. More symbols: \u2764\uFE0F\u2705."#;

fn benchmark_find_escape_char(c: &mut Criterion) {
    use json_escape::{token::ESCAPE_DECISION_TABLE, token::EscapeTokens};

    let mut group = c.benchmark_group("Find Escape Char");

    fn find_escape_char_plain(bytes: &[u8]) -> Option<usize> {
        bytes
            .iter()
            .position(|&b| ESCAPE_DECISION_TABLE[b as usize] != 0)
    }

    for (id, input) in [
        ("No Escapes", NO_ESCAPES),
        ("Sparse Escapes", SPARSE_ESCAPES),
        ("Dense Escapes", DENSE_ESCAPES),
        ("Unicode", UNICODE_ESCAPES_RAW),
    ]
    .iter()
    {
        group.bench_with_input(*id, input, |b, i| {
            b.iter(|| black_box(EscapeTokens::find_escape_char(black_box(i.as_bytes()))))
        });

        group.bench_with_input(format!("Plain/{id}"), input, |b, i| {
            b.iter(|| black_box(find_escape_char_plain(black_box(i.as_bytes()))))
        });
    }

    group.finish();
}

/// A macro to benchmark a function from both the main and `explicit` modules.
///
/// The benchmark logic is written once, and this macro generates both versions.
macro_rules! benchmark_pair {
    (
        // The criterion benchmark group, e.g., `&mut group`
        $group:expr,
        // The base name for this benchmark, e.g., "Iterate Only"
        $bench_name:literal,
        // The criterion input id and value from your loop, e.g., `(id, input)`
        ($input_id:expr, $input_val:expr),
        // The base name of the function to swap, e.g., `escape_str`
        $func_name:ident,
        // A closure containing the benchmark logic.
        // It receives the bencher, the input value, and the function to call.
        |$b:ident, $i:ident, $api_fn:ident| $body:block
    ) => {
        // --- Benchmark the main API ---
        $group.bench_with_input(
            BenchmarkId::new(format!("{}/Main", $bench_name), $input_id),
            $input_val,
            |$b, &$i| {
                // In this scope, `api_fn` is the main function (e.g., `escape_str`)
                let $api_fn = $func_name;
                $body
            },
        );

        // --- Benchmark the explicit API ---
        $group.bench_with_input(
            BenchmarkId::new(format!("{}/Explicit", $bench_name), $input_id),
            $input_val,
            |$b, &$i| {
                // In this scope, `api_fn` is the explicit version (e.g., `explicit::escape_str`)
                let $api_fn = explicit::$func_name;
                $body
            },
        );

        // --- Benchmark the explicit API ---
        $group.bench_with_input(
            BenchmarkId::new(format!("{}/Token", $bench_name), $input_id),
            $input_val,
            |$b, &$i| {
                // In this scope, `api_fn` is the explicit version (e.g., `explicit::escape_str`)
                let $api_fn = token::$func_name;
                $body
            },
        );
    };
}

/// Benchmarks for the `escape_str` functionality.
fn escape_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Escape");

    for (id, input) in [
        ("No Escapes", NO_ESCAPES),
        ("Sparse Escapes", SPARSE_ESCAPES),
        ("Dense Escapes", DENSE_ESCAPES),
        ("Unicode", UNICODE_ESCAPES_RAW),
    ]
    .iter()
    {
        // 1. Pure iterator performance (no allocation).
        // Measures the overhead of the iterator logic itself.
        benchmark_pair!(
            &mut group,
            "Iterate Only",
            (id, input),
            escape_str,
            |b, i, a_fn| {
                b.iter(|| {
                    for chunk in a_fn(i) {
                        black_box(chunk);
                    }
                })
            }
        );

        // 2. Collecting into a String (includes allocation).
        // A common use case that measures the full cost of creating an owned string.
        benchmark_pair!(
            &mut group,
            "Collect to String",
            (id, input),
            escape_str,
            |b, i, a_fn| {
                b.iter(|| {
                    let s: String = a_fn(i).collect();
                    black_box(s);
                })
            }
        );

        // 3. Writing to a sink using the `fmt::Display` implementation.
        // Measures performance for streaming scenarios without intermediate allocation.
        benchmark_pair!(
            &mut group,
            "Write to Sink",
            (id, input),
            escape_str,
            |b, i, a_fn| {
                b.iter(|| {
                    let mut sink = io::sink();
                    write!(sink, "{}", a_fn(i)).unwrap();
                    black_box(sink);
                })
            }
        );
    }

    // --- Main API ---

    // 4. Special case: `Cow::from` conversion, testing the optimization paths.
    // Test the `Cow::Borrowed` fast path where no allocation occurs.
    group.bench_function("Cow::from (Borrowed)", |b| {
        b.iter(|| {
            let cow: Cow<str> = escape_str(NO_ESCAPES).into();
            black_box(cow);
        })
    });

    // --- Explicit API ---
    group.bench_function("Cow::from (Borrowed)/Explicit", |b| {
        b.iter(|| {
            let cow: Cow<str> = explicit::escape_str(NO_ESCAPES).into();
            black_box(cow);
        })
    });

    // --- Main API ---

    // Test the `Cow::Owned` path where allocation is necessary.
    group.bench_function("Cow::from (Owned)", |b| {
        b.iter(|| {
            let cow: Cow<str> = escape_str(SPARSE_ESCAPES).into();
            black_box(cow);
        })
    });

    // --- Explicit API ---
    group.bench_function("Cow::from (Owned)/Explicit", |b| {
        b.iter(|| {
            let cow: Cow<str> = escape_str(SPARSE_ESCAPES).into();
            black_box(cow);
        })
    });

    group.finish();
}

/// Benchmarks for the `unescape` functionality.
fn unescape_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Unescape");

    for (id, input_escaped) in [
        ("No Escapes", NO_ESCAPES),
        ("Sparse Escapes", SPARSE_ESCAPES),
        ("Dense Escapes", DENSE_ESCAPES),
        ("Unicode", UNICODE_ESCAPES_ESCAPED),
    ]
    .iter()
    {
        // 1. Pure iterator performance (no allocation).
        // Measures the overhead of the unescaping and error-handling logic.
        benchmark_pair!(
            &mut group,
            "Iterate Only",
            (id, input_escaped),
            unescape,
            |b, i, a_fn| {
                b.iter(|| {
                    for r in a_fn(i) {
                        let _ = black_box(r);
                    }
                })
            }
        );

        // 2. Reading into a Vec via the `std::io::Read` implementation.
        // Measures the performance of streaming unescaped data.
        group.bench_with_input(
            BenchmarkId::new("Read to Vec", id),
            input_escaped,
            |b, &i| {
                b.iter(|| {
                    let mut reader = unescape(i);
                    let mut buf = Vec::with_capacity(i.len());
                    reader.read_to_end(&mut buf).unwrap();
                    black_box(buf);
                })
            },
        );

        // 3. Decoding to a UTF-8 String.
        // A primary use case that combines unescaping, allocation, and UTF-8 validation.
        benchmark_pair!(
            &mut group,
            "Decode UTF-8",
            (id, input_escaped),
            unescape,
            |b, i, a_fn| {
                b.iter(|| {
                    let s = a_fn(i).decode_utf8().unwrap();
                    black_box(s);
                })
            }
        );
    }

    group.finish();
}

/// Benchmarks the streaming unescaper against a traditional "buffer-then-process" approach.
fn unescape_streaming_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Unescape Stream vs Buffer");

    // --- Configuration ---
    const TOTAL_SIZE: usize = 1024 * 1024; // 1 MiB total data
    const CHUNK_SIZES: &[usize] = &[64, 1024, 16 * 1024]; // 64B, 1KiB, 16KiB chunks

    /// Helper to generate a large Vec<u8> by repeating a base string pattern.
    /// This version ensures that only whole copies of the base pattern are appended,
    /// preventing the data from ending in an incomplete escape sequence.
    /// Thus it might not be exactly 'size' big but never more than.
    fn generate_data(base: &str, size: usize) -> Vec<u8> {
        let mut data = Vec::with_capacity(size);
        let base_bytes = base.as_bytes();

        // This check is important for very small base strings to avoid an infinite loop.
        if base_bytes.is_empty() {
            return data;
        }

        // Only append whole copies of the base string.
        while data.len() + base_bytes.len() <= size {
            data.extend_from_slice(base_bytes);
        }

        data
    }
    
    // --- Benchmark Loop ---
    // Iterate over different types of input data.
    for (id, base_str) in [
        ("NoEscapes", NO_ESCAPES),
        ("SparseEscapes", SPARSE_ESCAPES),
        ("DenseEscapes", DENSE_ESCAPES),
        ("UnicodeEscapes", UNICODE_ESCAPES_ESCAPED),
    ]
    .iter()
    {
        let source_data = generate_data(base_str, TOTAL_SIZE);

        // Iterate over different chunk sizes for the simulated stream.
        for &chunk_size in CHUNK_SIZES {
            let bench_id = format!("{}/{}B_chunks", id, chunk_size);

            // --- 1. Streaming API Benchmark ---
            // Processes chunks as they "arrive" in a single pass.
            group.bench_with_input(
                BenchmarkId::new("Streaming", &bench_id),
                &(source_data.clone(), chunk_size),
                |b, (data, cs)| {
                    b.iter(|| {
                        let mut stream = UnescapeStream::new();
                        // Pre-allocate output to focus on unescaping, not output allocation.
                        let mut output = String::with_capacity(TOTAL_SIZE);

                        for chunk in data.chunks(*cs) {
                            let (boundary, iter) = stream.try_unescape_next(chunk).unwrap();
                            if let Some(c) = boundary {
                                output.push(c);
                            }
                            for token in iter {
                                match token.unwrap() {
                                    UnescapedToken::Unescaped(c) => output.push(c),
                                    UnescapedToken::Literal(s) => {
                                        // SAFETY: read part of chunk is valid utf8
                                        output.push_str(unsafe { str::from_utf8_unchecked(s) })
                                    }
                                }
                            }
                        }
                        stream.finish().unwrap();
                        black_box(output);
                    });
                },
            );

            // --- 2. Buffering (Alternative) Benchmark ---
            // First pass: collect all chunks. Second pass: unescape.
            group.bench_with_input(
                BenchmarkId::new("Buffering", &bench_id),
                &(source_data.clone(), chunk_size),
                |b, (data, cs)| {
                    b.iter(|| {
                        // Step 1: Collect all chunks into a single, large buffer.
                        let mut full_buffer = Vec::with_capacity(TOTAL_SIZE);
                        for chunk in data.chunks(*cs) {
                            full_buffer.extend_from_slice(chunk);
                        }

                        // Step 2: Unescape the complete buffer using the base API.
                        let result = unescape(&full_buffer).decode_utf8().unwrap();
                        black_box(result);
                    });
                },
            );
        }
    }

    group.finish();
}

// --- Structs for the Nested JSON Benchmark ---

// Represents the outer JSON object containing the escaped string.
#[derive(Deserialize)]
struct OuterPayload<'a> {
    #[serde(borrow)]
    json_string: &'a serde_json::value::RawValue,
}

// Represents the complex inner JSON that we want to parse.
#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct InnerPayload {
    id: u64,
    name: String,
    is_active: bool,
    scores: Vec<i32>,
    metadata: HashMap<String, String>,
}

// --- Helper function to generate test data ---

/// Creates a complex `InnerPayload` and embeds its serialized, escaped form
/// into an `OuterPayload`'s JSON representation.
fn generate_nested_json_string(size: usize) -> String {
    let mut metadata = HashMap::new();
    for i in 0..size / 2 {
        metadata.insert(format!("key_{i}"), format!("value_{i}"));
    }

    let inner = InnerPayload {
        id: 12345,
        name: "Benchmark Payload".to_string(),
        is_active: true,
        scores: (0..size as i32).collect(),
        metadata,
    };

    // Serialize the inner payload to a JSON string.
    let inner_json_str = serde_json::to_string(&inner).unwrap();

    // Create the outer JSON object, which will automatically escape the inner string.
    let outer_json = serde_json::json!({
        "json_string": inner_json_str
    });

    serde_json::to_string(&outer_json).unwrap()
}

/// Benchmarks parsing a JSON string embedded within another JSON object.
fn nested_json_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Nested JSON Parsing");

    // We'll test with different sizes of inner JSON data.
    for &size in &[10, 100, 1000] {
        let nested_json = generate_nested_json_string(size);

        // --- Method 1: Intermediate Heap Allocation (The Standard Way) ---
        // This method fully unescapes the inner string into a new `String` on the heap
        // before passing it to the parser.
        group.bench_with_input(
            BenchmarkId::new("Heap Allocation", size),
            &nested_json,
            |b, data| {
                b.iter(|| {
                    // 1. Parse outer to get the raw string slice
                    let outer: OuterPayload<'_> = serde_json::from_str(data).unwrap();

                    // 2. Deserialize from the raw slice into a new `String`.
                    // THIS IS THE HEAP ALLOCATION WE WANT TO AVOID.
                    let unescaped_string: String =
                        serde_json::from_str(outer.json_string.get()).unwrap();

                    // 3. Parse the newly allocated string
                    let inner: InnerPayload = serde_json::from_str(&unescaped_string).unwrap();

                    black_box(inner);
                })
            },
        );

        // --- Method 2: Streaming with json_escape ---
        // This method uses `unescape_quoted` as a `Read` adapter, allowing `serde_json`
        // to parse the unescaped bytes on the fly without an intermediate string.
        group.bench_with_input(
            BenchmarkId::new("Streaming (json_escape)", size),
            &nested_json,
            |b, data| {
                b.iter(|| {
                    // 1. Parse outer to get the raw string slice
                    let outer: OuterPayload<'_> = serde_json::from_str(data).unwrap();

                    // 2. Create the streaming reader (NO HEAP ALLOCATION)
                    let reader = unescape_quoted(outer.json_string.get());

                    // 3. Parse directly from the reader
                    let inner: InnerPayload = serde_json::from_reader(reader).unwrap();

                    black_box(inner);
                })
            },
        );
    }

    group.finish();
}

/// Note: This is not a 1-to-1 comparison as serde_json performs a full JSON parse/serialization,
/// but it provides a useful real-world performance baseline.
fn comparison_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Comparison vs serde_json");

    for (id, input) in [
        ("No Escapes", NO_ESCAPES),
        ("Sparse Escapes", SPARSE_ESCAPES),
        ("Unicode", UNICODE_ESCAPES_RAW),
    ]
    .iter()
    {
        // Escaping comparison
        group.bench_with_input(
            BenchmarkId::new("escape/serde_json::to_string", id),
            input,
            |b, &i| {
                b.iter(|| {
                    // serde_json::to_string wraps the string in quotes and escapes it.
                    black_box(serde_json::to_string(i).unwrap());
                })
            },
        );

        // Unescaping comparison
        // We must first create a valid JSON string literal for serde_json to parse.
        let json_literal = format!(r#""{}""#, escape_str(input).collect::<String>());

        group.bench_with_input(
            BenchmarkId::new("unescape/serde_json::from_str", id),
            &json_literal,
            |b, i| {
                b.iter(|| {
                    // serde_json::from_str parses the quoted string and unescapes it.
                    let s: String = serde_json::from_str(i).unwrap();
                    black_box(s);
                })
            },
        );
    }
    group.finish();
}

// Register the benchmark groups.
criterion_group!(
    benches,
    benchmark_find_escape_char,
    escape_benchmarks,
    unescape_benchmarks,
    unescape_streaming_benchmarks,
    nested_json_benchmarks,
    comparison_benchmarks
);
criterion_main!(benches);
