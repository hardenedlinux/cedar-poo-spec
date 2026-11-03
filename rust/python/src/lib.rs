//! Native Python consumer facade; all Cedar semantics remain in the shared runtime.
mod bindings;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
