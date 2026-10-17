// A callback popping the mapped array through an optional chain: the chain's
// body runs `pop` where the receiver is present, so the callback is bounded
// by `pop`'s footprint and the result has holes.
export function drained(xs: number[], ys: number[] | undefined): number[] {
  const target = ys ?? xs;
  return xs.map((x: number): number => (target?.pop() ?? 0) + x);
}
