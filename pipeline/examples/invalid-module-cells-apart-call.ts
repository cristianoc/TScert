// Two module cells filled in turn by `??=`, then a call that may write
// either: a call at a footprint letting a value change may write any
// module cell, so past it the first is read at its contract,
// `number[] | null`, and `reset` leaves `null` in it.
let runs: number[] | null = null;
let remaps: number[] | null = null;

export function reset(): void {
  runs = null;
}

export function unpack(n: number, f: () => void): number[] {
  runs ??= [n];
  remaps ??= [n + 1];
  f();
  return runs;
}
