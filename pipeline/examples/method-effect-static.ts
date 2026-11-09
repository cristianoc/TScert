// A static method stating the empty footprint: its binding is checked at
// its annotation, statement included, and a `map` callback calling it is
// within the empty footprint.
export class Units {
  static cents(n: number): Modifies<{}, number> {
    return n * 100;
  }
}

export function cents(xs: number[]): number[] {
  const r: number[] = xs.map((x) => Units.cents(x));
  return r;
}
