use super::encode;

#[test]
fn streaming_bytes_match_original_json_line() {
    for value in [
        serde_json::json!({"escaped":"\n\"\\λ", "nested":[null, true, 123]}),
        serde_json::json!({}),
        serde_json::json!([1, 2, 3]),
    ] {
        let mut output = Vec::new();
        encode(&mut output, &value).unwrap();
        assert_eq!(
            output,
            format!("{}\n", serde_json::to_string(&value).unwrap()).as_bytes()
        );
    }
}

#[test]
fn output_failure_is_not_a_successful_replay() {
    struct Broken;
    impl std::io::Write for Broken {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("broken output"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    assert!(
        encode(Broken, &serde_json::json!({}))
            .unwrap_err()
            .contains("broken output")
    );
}
