// A function declaration stating the empty footprint whose body pops the
// array it is handed: its unit is checked at its statement, and the pop
// changes a store it did not allocate (run under Node: a `map` callback
// calling it leaves a hole).
export function bump(xs: number[], x: number): Modifies<{}, number> {
  xs.pop();
  return x;
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => bump(xs, x));
  return r;
}
