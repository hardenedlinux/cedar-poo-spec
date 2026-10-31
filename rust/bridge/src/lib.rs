//! Command-line application for Cedar conformance checks.
mod benchmark;
mod benchmark_inventory;
mod catalog;
mod catalog_input;
mod catalog_observation;
pub mod cli;
mod financial;
mod output;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());

mod allocation;
