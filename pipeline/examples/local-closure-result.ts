// A local closure without a result annotation: its result is what its body
// returns, proposed by the producer and checked by Lean against the body.
// Passed to a callback offered more parameters, it is claimed at that
// signature too; called directly, at its own.
export function difference(xs: [number, number][]): number {
  const acc = (p: number | null, c: [number, number]) => {
    return p !== null ? p - c[1] : c[1];
  };
  const first: number = acc(null, [0, 1]);
  return xs.reduce(acc, null) ?? first;
}

export function half(x: number): number {
  const f = (y: number) => y / 2;
  return f(x);
}

// Inside a method, as in a mapper's mapEntry: sort, then reduce at an
// explicit instance, then `??`.
export class Minus {
  apply(values: [number, number][]): number {
    const acc = (p: number | null, c: [number, number]) => {
      return p !== null ? p - c[1] : c[1];
    };
    return values.sort().reduce<number | null>(acc, null) ?? 0;
  }
}
