//! Canonical receipt hashing: borrow existing Values and write escaped strings directly.
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::io::{self, Write};

pub(crate) fn json_sha256(value: &impl Serialize) -> Result<String, String> {
    let value = serde_json::to_value(value).map_err(|error| error.to_string())?;
    value_sha256(&value)
}

pub(crate) fn value_sha256(value: &Value) -> Result<String, String> {
    let mut writer = HashWriter {
        digest: Sha256::new(),
        buffer: [0; 1024],
        used: 0,
    };
    write_canonical_json(value, &mut writer)?;
    writer.flush().map_err(|error| error.to_string())?;
    let digest = writer.digest.finalize();
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[usize::from(byte >> 4)] as char);
        encoded.push(HEX[usize::from(byte & 15)] as char);
    }
    Ok(encoded)
}

// Stack buffering avoids a full canonical payload and tiny SHA update calls.
struct HashWriter {
    digest: Sha256,
    buffer: [u8; 1024],
    used: usize,
}
impl Write for HashWriter {
    fn write(&mut self, mut bytes: &[u8]) -> io::Result<usize> {
        let length = bytes.len();
        while !bytes.is_empty() {
            if self.used == 0 && bytes.len() >= self.buffer.len() {
                self.digest.update(bytes);
                break;
            }
            let count = bytes.len().min(self.buffer.len() - self.used);
            self.buffer[self.used..self.used + count].copy_from_slice(&bytes[..count]);
            self.used += count;
            bytes = &bytes[count..];
            if self.used == self.buffer.len() {
                self.flush()?;
            }
        }
        Ok(length)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.digest.update(&self.buffer[..self.used]);
        self.used = 0;
        Ok(())
    }
}
fn write_canonical_json(value: &Value, output: &mut impl Write) -> Result<(), String> {
    match value {
        Value::Null => output.write_all(b"null").map_err(|e| e.to_string()),
        Value::Bool(v) => output
            .write_all(if *v { b"true" } else { b"false" })
            .map_err(|e| e.to_string()),
        Value::Number(v) => output
            .write_all(v.to_string().as_bytes())
            .map_err(|e| e.to_string()),
        Value::String(v) => serde_json::to_writer(output, v).map_err(|e| e.to_string()),
        Value::Array(values) => {
            output.write_all(b"[").map_err(|e| e.to_string())?;
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    output.write_all(b",").map_err(|e| e.to_string())?;
                }
                write_canonical_json(value, output)?;
            }
            output.write_all(b"]").map_err(|e| e.to_string())
        }
        Value::Object(values) => {
            output.write_all(b"{").map_err(|e| e.to_string())?;
            if values.keys().is_sorted() {
                write_entries(values.iter(), output)?;
            } else {
                let mut entries = values.iter().collect::<Vec<_>>();
                entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
                write_entries(entries.into_iter(), output)?;
            }
            output.write_all(b"}").map_err(|e| e.to_string())
        }
    }
}
fn write_entries<'a>(
    entries: impl Iterator<Item = (&'a String, &'a Value)>,
    output: &mut impl Write,
) -> Result<(), String> {
    for (index, (key, value)) in entries.enumerate() {
        if index > 0 {
            output.write_all(b",").map_err(|e| e.to_string())?;
        }
        serde_json::to_writer(&mut *output, key).map_err(|e| e.to_string())?;
        output.write_all(b":").map_err(|e| e.to_string())?;
        write_canonical_json(value, output)?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "../tests/unit/canonical.rs"]
mod tests;
