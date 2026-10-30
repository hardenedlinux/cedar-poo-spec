//! Command-line application for Cedar conformance checks.
mod benchmark;
mod catalog;
mod catalog_observation;
pub mod cli;
mod financial;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());

mod allocation;
