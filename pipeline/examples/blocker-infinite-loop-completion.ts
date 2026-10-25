// A loop with no exit needs no implicit return obligation.
// Census functions:
// namespace-members.mts#written.
export function use(): boolean {
  for (;;) {}
}
