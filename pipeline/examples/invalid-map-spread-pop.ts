// A `map` callback spreading an array its spread operand pops first: the
// spread part reads a store, but its operand runs `pop` on the array being
// mapped, which bounds the callback by nothing, so `map` takes its signature
// with holes.
export function drained(xs: number[]): number[] {
  return xs.map(
    (x: number): number => [...(xs.pop() === undefined ? [] : xs)].length + x,
  );
}
