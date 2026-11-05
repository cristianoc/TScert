// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): line-breaks.ts#unpackClasses.
// Two module cells filled in turn by `??=`, then both passed on: two module
// cells are two locations, so the write of the second keeps the first's
// contents, an array.
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
