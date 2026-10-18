// `Object.values`, `Object.entries` and `Object.getOwnPropertyDescriptor`
// hand an object's own field values to the program; their parameter is the
// family of non-host values (COMPILER-API.md, "Restricted values"), which an
// operand whose type names an invariant field meets. `console.log` takes primitives. TypeScript selects the `{}`
// overloads at an interface, which has no implicit index signature.
interface R {
  a: number;
}
export function values(o: R): number {
  return Object.values(o).length;
}
export function entries(o: R | null): number {
  if (o === null) return 0;
  return Object.entries(o).length;
}
export function descriptor(o: { a: number }): boolean {
  return Object.getOwnPropertyDescriptor(o, "a") !== undefined;
}
export function log(n: number, s: string): void {
  console.log(n, s);
}
// Key enumeration is transparent: a fresh array of strings. A member read at
// an enumerated key reads only the stated member the key is tested to be.
export function keyed(o: { readonly a: number }): unknown[] {
  return Object.keys(o).map((k) => (k === "a" ? o[k] : undefined));
}
