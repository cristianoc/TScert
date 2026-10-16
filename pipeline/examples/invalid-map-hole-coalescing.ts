// A hole is permitted by the input element contract, but map skips it.
// Coalescing a visited value cannot fill a position whose callback never runs.
export function coalescingCallback(xs: (number | undefined)[]): number[] {
  return xs.map((value?: number): number => value ?? 0);
}
