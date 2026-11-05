// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): line-breaks.ts#unpackClasses.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim, a cell read at its contract.
// Two module cells filled in turn by `??=`, then both passed on: the write
// of the second may, as far as the function can tell, be a write of the
// first, since a module's cells are separated by no fact, so the first is
// read at its contract, `number[] | null`.
let runs: number[] | null = null;
let remaps: number[] | null = null;

function count(a: number[], b: number[]): number {
  return a.length + b.length;
}

export function unpack(n: number): number {
  runs ??= [n];
  remaps ??= [n + 1];
  return count(runs, remaps);
}
