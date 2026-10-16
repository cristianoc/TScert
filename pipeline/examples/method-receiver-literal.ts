// A fresh literal passed to a prototype member at the binder its receiver
// fixes (`push` of a `D[]`, whose `T` is `D`) is built at what the receiver
// makes it: the arm of `D` its discriminant names.
type D = { kind: "a"; v: number } | { kind: "b"; w: string };
export function add(items: D[]): number {
  return items.push({ kind: "a", v: 1 }, { kind: "b", w: "x" });
}
