//! Bounded output buffer; no whole serialized response String allocation.
use serde::Serialize;
use std::io::{self, BufWriter, Write};

fn encode(mut writer: impl Write, value: &impl Serialize) -> Result<(), String> {
    serde_json::to_writer(&mut writer, value).map_err(|error| error.to_string())?;
    writer.write_all(b"\n").map_err(|error| error.to_string())?;
    writer.flush().map_err(|error| error.to_string())
}

pub(crate) fn write_json(value: &impl Serialize) -> Result<(), String> {
    encode(BufWriter::new(io::stdout().lock()), value)
}

#[cfg(test)]
#[path = "../tests/unit/output.rs"]
mod tests;
