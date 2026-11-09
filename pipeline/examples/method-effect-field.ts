// A method field holding a module function at `typeof` its declaration, the
// convention TScert's own `Gate` follows: the field's contract reads the
// declaration's statement, the initializer meets it, and a `map` callback
// calling the field is within the empty footprint, so the result is dense.
export function scaled(this: Scale, n: number): Modifies<{}, number> {
  return n * this.factor;
}

export class Scale {
  factor: number = 2;
  scaled: typeof scaled = scaled;
}

export function all(s: Scale, xs: number[]): number[] {
  const r: number[] = xs.map((x) => s.scaled(x));
  return r;
}
