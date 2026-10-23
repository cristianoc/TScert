// The merges a spread, an object rest and `Object.assign` lower to copy their
// operands' own keys: each operand's type excludes host values
// (HOST-FAMILIES.md, "Excluding host values"), by an invariant field, a closed
// literal, a dictionary, a primitive or a writable array.
export function field(o: { a: number }): { a: number } {
  return { ...o };
}
export function closed(): { a: number } {
  const o = { a: 1 };
  return { ...o };
}
export function dictionary(d: { readonly [k: string]: number }): {
  readonly [k: string]: number;
} {
  return { ...d };
}
export function primitive(n: number): {} {
  return { ...n };
}
export function union(o: { a: number } | { b: string } | null): {} {
  return { ...o };
}
export function writableArray(xs: number[]): {} {
  return { ...xs };
}
export function rest(o: { a: number; b: string }): { b: string } {
  const { a, ...r } = o;
  return r;
}
export function assign(): number {
  const t = { a: 1 };
  Object.assign(t, { b: 2 });
  return t.a;
}
