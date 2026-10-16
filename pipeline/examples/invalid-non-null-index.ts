// A dictionary read at a number key is admitted, at the index's type or
// `undefined`: the object may lack the key, and `!` does not rule
// `undefined` out.
export function wrong(v: { [k: string]: number }, n: number): number {
  return v[n]!;
}
