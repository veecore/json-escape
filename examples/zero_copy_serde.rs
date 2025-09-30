//! Advanced integration: zero-copy nested JSON parsing with `serde_json::RawValue`.

use json_escape::unescape_quoted;
use serde::Deserialize;
use serde_json::value::RawValue;

#[derive(Deserialize, Debug)]
#[allow(dead_code)]
struct InnerPayload {
    user_id: u64,
    items: Vec<String>,
}

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

    // Parse outer structure first.
    let outer: OuterPayload = serde_json::from_str(response_body).unwrap();

    // Create a reader that streams the unescaped inner payload.
    let reader = unescape_quoted(outer.payload.get());

    // Deserialize inner payload directly, without an intermediate String.
    let inner: InnerPayload = serde_json::from_reader(reader).unwrap();

    println!("Outer transaction: {}", outer.transaction_id);
    println!("Inner payload: {:?}", inner);
}
