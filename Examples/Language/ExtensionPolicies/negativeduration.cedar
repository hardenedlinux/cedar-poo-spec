// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: negative-duration
permit(
  principal == User::"alice",
  action == Action::"view",
  resource == Document::"doc"
) when {
  context.value == duration("-2h")
};
