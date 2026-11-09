// A class method stating it changes no location, whose body pops the array
// it is handed: the method's code is checked at its statement, and the pop
// changes a store it did not allocate. Were the statement read as written, a
// `map` callback calling the method would take `map`'s dense signature
// (run under Node: the pop leaves a hole in the result).
export class Bump {
  bump(xs: number[], x: number): Modifies<{}, number> {
    xs.pop();
    return x;
  }
}

export function wrong(b: Bump, xs: number[]): number[] {
  const r: number[] = xs.map((x) => b.bump(xs, x));
  return r;
}
