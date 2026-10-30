.kind == "native-catalog-benchmark" and .build_profile == "release" and .warmup == 1 and
(.samples | length) == 3 and all(.samples[];
  .rows == 1280 and .runtime.authorization_calls == 2560 and
  .runtime.prepared_revisions == 221 and .runtime.source_policy_loads == 221 and
  (.catalog.entries | length) == 51 and .catalog.retained_manifests == 3 and
  (.runtime.revision_source_load_ns + .runtime.revision_render_ns +
   .runtime.revision_text_parse_ns + .runtime.revision_normalize_ns +
   .runtime.revision_compare_ns + .runtime.revision_hash_ns) <= .runtime.revision_preparation_ns and
  .runtime.revision_render_ns > 0 and .runtime.revision_text_parse_ns > 0 and
  .runtime.revision_normalize_ns > 0 and
  .runtime.entity_slot_peak == 1 and .runtime.entity_parse_calls > 0 and
  .runtime.entity_reuses > 0 and
  (.runtime.entity_parse_calls + .runtime.entity_reuses) == .rows)
