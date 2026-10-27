// A call of a member read through `!` passes the member's object as its
// receiver, as an unwrapped call does; a call of the asserted value would
// pass none, so the parser refuses it rather than lose the receiver.
export function wrapped(fs: readonly (() => number)[], i: number): number {
  return fs[i]!();
}
