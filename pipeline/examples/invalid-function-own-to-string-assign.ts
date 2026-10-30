// `Object.assign` of an arrow and a literal gives the arrow each key of the
// literal: here a `toString` that is a string, which a function's lookup
// finds before `Function.prototype`'s. The literal's key is refused
// (SOURCE-CONTRACTS.md, "Function.prototype.toString"). Under Node,
// `typeof g.toString` is `"string"`, and `g.toString()` throws.
export const g = Object.assign((): number => 1, { toString: "x" });

export function text(f: () => number): string {
  return f.toString();
}
