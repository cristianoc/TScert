// Every object inherits `toString` from `Object.prototype`, which the model
// does not hold: the model's own-key test would answer `false`.
export function printable(x: { a: number }): boolean {
  return "toString" in x;
}
