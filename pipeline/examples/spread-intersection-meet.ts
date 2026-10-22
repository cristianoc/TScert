// Spreads of a value of an intersection: the value is of every operand, so
// its copy is the meet of one arm of each, `(A | B) & C` read as
// `(A & C) | (B & C)`, a key two operands state held at the field within the
// other's, required where either requires it.
type Part =
  | { name: PropertyKey; e: number; computed?: true }
  | { spread: number };
export function computed(p: Part & { name: PropertyKey }): Part {
  return { ...p, computed: true };
}
type Tagged = { k: "a"; name: string } | { k: "b" };
export function tagged(
  x: Tagged & { name: "x" },
): { k: "a"; name: "x" } | { k: "b"; name: "x" } {
  return { ...x };
}
export function narrowed(x: { k: string; t: number } & { readonly k: "a" }): {
  k: "a";
  t: number;
} {
  return { ...x };
}
export function required(x: { k?: string } & { k: "a"; t: number }): {
  k: "a";
  t: number;
} {
  return { ...x };
}
export function three(
  x: { k: string; a: number } & { k: "a" | "b" } & {
    readonly k: "a";
    b: boolean;
  },
): { k: "a"; a: number; b: boolean } {
  return { ...x };
}
// A primitive arm meets no record: `string & { b: number }` has no value.
export function primitive(x: (string | { a: number }) & { b: number }): {
  a: number;
  b: number;
} {
  return { ...x };
}
// A class instance's own field is copied, its method is not.
class Counter {
  count: number = 0;
  next(): number {
    return this.count + 1;
  }
}
export function instance(c: Counter & { tag: string }): {
  count: number;
  tag: string;
} {
  return { ...c };
}
export function written(x: { k: string; t: number } & { k: "a" }): {
  k: "b";
  t: number;
} {
  return { ...x, k: "b" };
}
export function rest(
  x: ({ k: "a"; v: number } | { k: "b" }) & { k: string; w: string },
): { w: string } {
  const { k, ...others } = x;
  return others;
}
// The copy's `k` is the operands' "a"; a literal elsewhere states "b".
export function widened(x: { k: string; t: number } & { k: "a" }): {
  readonly k: string;
  t: number;
} {
  return { ...x };
}
export function other(): { k: "b"; t: number } {
  return { k: "b", t: 0 };
}
