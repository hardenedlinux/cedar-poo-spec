// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: ip-functions
permit(
  principal == User::"alice",
  action == Action::"view",
  resource == Document::"doc"
) when {
  (context.value == ip("10.1.2.3")) && (context.value.isIpv4() && ((!context.value.isIpv6()) && ((!context.value.isLoopback()) && ((!context.value.isMulticast()) && (context.value.isInRange(ip("10.0.0.0/8")) && true)))))
};
