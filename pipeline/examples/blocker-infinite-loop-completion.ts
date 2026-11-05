// A loop with no exit has no implicit return obligation after it.
// Census functions:
// namespace-members.mts#written.
export function use(): boolean {
  for (;;) {}
}
