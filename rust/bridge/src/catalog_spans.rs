//! Linear span index for already validated JSON; never a JSON validator.
use std::collections::BTreeMap;

fn whitespace(bytes: &[u8], index: &mut usize) {
    while bytes.get(*index).is_some_and(u8::is_ascii_whitespace) {
        *index += 1;
    }
}
fn string_end(bytes: &[u8], mut index: usize) -> Option<usize> {
    if bytes.get(index) != Some(&b'"') {
        return None;
    }
    index += 1;
    while let Some(byte) = bytes.get(index) {
        match byte {
            b'"' => return Some(index + 1),
            b'\\' => index += 2,
            _ => index += 1,
        }
    }
    None
}
fn value_end(bytes: &[u8], start: usize) -> Option<usize> {
    let first = *bytes.get(start)?;
    if first == b'"' {
        return string_end(bytes, start);
    }
    if first != b'[' && first != b'{' {
        let mut index = start;
        while bytes
            .get(index)
            .is_some_and(|b| !b.is_ascii_whitespace() && *b != b',' && *b != b'}')
        {
            index += 1;
        }
        return (index > start).then_some(index);
    }
    let (mut index, mut depth) = (start, 0usize);
    while let Some(byte) = bytes.get(index) {
        match byte {
            b'"' => {
                index = string_end(bytes, index)?;
                continue;
            }
            b'[' | b'{' => depth += 1,
            b']' | b'}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index + 1);
                }
            }
            _ => {}
        }
        index += 1;
    }
    None
}
pub(super) fn object(input: &str) -> Option<BTreeMap<String, &str>> {
    let bytes = input.as_bytes();
    let mut index = 0;
    whitespace(bytes, &mut index);
    if bytes.get(index) != Some(&b'{') {
        return None;
    }
    index += 1;
    let mut result = BTreeMap::new();
    loop {
        whitespace(bytes, &mut index);
        if bytes.get(index) == Some(&b'}') {
            return Some(result);
        }
        let key_end = string_end(bytes, index)?;
        let key = serde_json::from_str::<String>(input.get(index..key_end)?).ok()?;
        index = key_end;
        whitespace(bytes, &mut index);
        if bytes.get(index) != Some(&b':') {
            return None;
        }
        index += 1;
        whitespace(bytes, &mut index);
        let end = value_end(bytes, index)?;
        result.insert(key, input.get(index..end)?);
        index = end;
        whitespace(bytes, &mut index);
        match bytes.get(index) {
            Some(b',') => index += 1,
            Some(b'}') => return Some(result),
            _ => return None,
        }
    }
}
