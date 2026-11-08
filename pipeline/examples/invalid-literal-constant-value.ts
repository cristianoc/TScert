// A module constant whose literal is 1, not 0: the binding assigned it is 1,
// the invariant `lastKind < 16 * flags.length` fails on the path that pushes
// nothing, and the write `flags[flags.length - 1]` below an empty list would
// read `undefined` at `number` (run under Node: `marks([0x20])` throws no
// error but `flags[-1]!` is `undefined`).
export const ONE = 1;

export function marks(codes: number[]): number[] {
  const flags: number[] = [];
  let lastKind = -1;
  /** @invariant safeInteger(lastKind) && lastKind < 16 * flags.length */
  for (let i = 0; i < codes.length; i++) {
    lastKind = ONE;
    flags[flags.length - 1] = flags[flags.length - 1]! | 0x80;
  }
  return flags;
}
