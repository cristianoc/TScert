// A chain of `&&` (or of `||`) reads as right-nested, `a && (b && c)`:
// the same evaluation and value, and each operand sees what every earlier
// one answered, in a condition and in a value alike.
type V = null | number | { a: number };

export function inCondition(x: V): number {
  if (typeof x === "object" && x !== null && x.a > 0) return x.a;
  return 0;
}

export function inValue(x: V): boolean {
  return typeof x === "object" && x !== null && x.a > 0;
}

export function orChain(x: V): boolean {
  return typeof x !== "object" || x === null || x.a > 0;
}
