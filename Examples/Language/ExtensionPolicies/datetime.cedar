// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: datetime-functions
permit(
  principal == User::"alice",
  action == Action::"view",
  resource == Document::"doc"
) when {
  (context.value == datetime("2026-01-02T03:04:05.000Z")) && ((context.window == duration("2h")) && ((context.value.offset(context.window) == datetime("2026-01-02T05:04:05.000Z")) && ((context.value.durationSince(datetime("2026-01-02T01:04:05.000Z")) == duration("2h")) && ((context.value.toDate() == datetime("2026-01-02")) && ((context.value.toTime() == duration("3h4m5s")) && ((context.window.toMilliseconds() == 7200000) && ((context.window.toSeconds() == 7200) && ((context.window.toMinutes() == 120) && ((context.window.toHours() == 2) && ((context.window.toDays() == 0) && true))))))))))
};
