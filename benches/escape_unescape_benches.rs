use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use json_escape::{escape_str, unescape, unescape_quoted};
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
        group.bench_with_input(BenchmarkId::new("Iterate Only", id), input, |b, &i| {
            b.iter(|| {
                for chunk in escape_str(i) {
                    black_box(chunk);
                }
            })
        });

        // 2. Collecting into a String (includes allocation).
        // A common use case that measures the full cost of creating an owned string.
        group.bench_with_input(BenchmarkId::new("Collect to String", id), input, |b, &i| {
            b.iter(|| {
                let s: String = escape_str(i).collect();
                black_box(s);
            })
        });

        // 3. Writing to a sink using the `fmt::Display` implementation.
        // Measures performance for streaming scenarios without intermediate allocation.
        group.bench_with_input(BenchmarkId::new("Write to Sink", id), input, |b, &i| {
            b.iter(|| {
                let mut sink = io::sink(); // A writer that discards all data.
                write!(sink, "{}", escape_str(i)).unwrap();
                black_box(sink);
            })
        });
    }

    // 4. Special case: `Cow::from` conversion, testing the optimization paths.
    // Test the `Cow::Borrowed` fast path where no allocation occurs.
    group.bench_function("Cow::from (Borrowed)", |b| {
        b.iter(|| {
            let cow: Cow<str> = escape_str(NO_ESCAPES).into();
            black_box(cow);
        })
    });

    // Test the `Cow::Owned` path where allocation is necessary.
    group.bench_function("Cow::from (Owned)", |b| {
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
        group.bench_with_input(
            BenchmarkId::new("Iterate Only", id),
            input_escaped,
            |b, &i| {
                b.iter(|| {
                    for r in unescape(i) {
                        let _ = black_box(r);
                    }
                })
            },
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
        group.bench_with_input(
            BenchmarkId::new("Decode UTF-8", id),
            input_escaped,
            |b, &i| {
                b.iter(|| {
                    let s = unescape(i).decode_utf8().unwrap();
                    black_box(s);
                })
            },
        );
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

        // --- Method 2: Streaming with json_escape (Your Optimal Way) ---
        // This method uses `unescape_quoted` as a `Read` adapter, allowing `serde_json`
        // to parse the unescaped bytes on the fly without an intermediate string.
        //
        // NOTE: Turned out to be slower. Why? serde_json::from_reader is not as optimized
        // as serde_json::from_str
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
    escape_benchmarks,
    unescape_benchmarks,
    nested_json_benchmarks,
    comparison_benchmarks
);
criterion_main!(benches);
