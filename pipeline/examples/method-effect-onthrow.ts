// A method stating the empty footprint on a throw too: it throws before
// changing anything, so its code meets the statement on both exits, and a
// `map` callback catching its throw starts its handler within the empty
// footprint of its entry, so the result is dense.
export class Check {
  positive(n: number): Modifies<{ onThrow: true }, number> {
    if (n < 0) throw new Error("negative");
    return n;
  }
}

export function clamped(c: Check, xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    try {
      return c.positive(x);
    } catch {
      return 0;
    }
  });
  return r;
}
