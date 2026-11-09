// Two methods stating the empty footprint, each calling the other through
// `this`: each body is checked at its statement with the other read at its
// own, and a `map` callback calling one is within the empty footprint.
export class Parity {
  even(n: number): Modifies<{}, boolean> {
    return n === 0 ? true : this.odd(n - 1);
  }
  odd(n: number): Modifies<{}, boolean> {
    return n === 0 ? false : this.even(n - 1);
  }
}

export function evens(p: Parity, xs: number[]): boolean[] {
  const r: boolean[] = xs.map((x) => p.even(x));
  return r;
}
