// Finite acquisition projection of Attackers.Trace. Rules come from checked POO slots.
module attackers_capabilities {
  pure def canLearn(known: Set[str], rules: Set[{ needs: Set[str], grants: str }], target: str): bool =
    rules.exists(rule => rule.grants == target and rule.needs.subseteq(known))
}
