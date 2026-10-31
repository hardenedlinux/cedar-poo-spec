use super::{decode, value};
use serde_json::Value;
use std::collections::BTreeMap;

fn original(input: &str) -> Result<BTreeMap<String, Value>, String> {
    serde_json::from_str(input).map_err(|e| e.to_string())
}
fn borrowed(input: &str) -> Result<BTreeMap<String, Value>, String> {
    decode(input)?
        .into_iter()
        .map(|(key, raw)| Ok((key, value(raw)?)))
        .collect()
}
#[test]
fn duplicate_normalization_numeric_and_full_input_error_precedence_match() {
    for input in [
        "{}",
        "null",
        "123 junk",
        "true",
        "[]",
        "{",
        "{\"x\":1e400,\"x\":0}",
        "{\"x\":[1e400,]}",
        "{\"x\":{\"a\":1,\"a\":2},\"x\":{\"a\":3}}",
        "{\"x\":\"\\ud800\"}",
        "{\"x\":18446744073709551616}",
        "{\"x\":-0.0} trailing",
        "{\"x\":0,\"late\":1e400}",
        "{\"x\":\"λ\\n\\\"\"}",
    ] {
        assert_eq!(borrowed(input), original(input), "{input}");
    }
}
#[test]
fn every_truncated_prefix_and_byte_corruption_matches_original_parser() {
    let fixture = r#"{"a":{"cases":[{"expected":"deny","expected":"allow","n":-123.45e-2,"s":"a\n\u0062"}]},"z":[true,false,null,42]}"#;
    for end in 0..=fixture.len() {
        let input = &fixture[..end];
        assert_eq!(borrowed(input), original(input), "prefix {end}");
    }
    for index in 0..fixture.len() {
        for byte in [b' ', b'"', b']', b'{', b'0', b'\\', b'x'] {
            let mut input = fixture.as_bytes().to_vec();
            input[index] = byte;
            let input = String::from_utf8(input).unwrap();
            assert_eq!(borrowed(&input), original(&input), "byte {index} -> {byte}");
        }
    }
    for depth in [126, 127, 128, 129, 256] {
        let input = format!("{{\"x\":{}{}}}", "[".repeat(depth), "]".repeat(depth));
        assert_eq!(borrowed(&input), original(&input), "depth {depth}");
    }
}

#[test]
fn private_tokens_escaped_keys_and_unicode_keep_plain_value_semantics() {
    for input in [
        r#"{"x":{"$serde_json::private::RawValue":"not JSON"}}"#,
        r#"{"x":{"$serde_json::private::Number":"NaN"}}"#,
        r#"{"\u0078":{"n":-0.0},"x":{"n":0.0}}"#,
        r#"{"λ":{"a":[{"quote":"\\\"{}[]"}]}}"#,
    ] {
        assert_eq!(borrowed(input), original(input));
    }
}
