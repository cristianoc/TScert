declare const marker: unique symbol;
type Marked = { readonly [marker]: true };
export function first(xs: [number, number] & Marked): number {
  return xs[0];
}
// An array may own a key its prototype does not provide: the tuple's meet
// with `Marked` is inhabited, its marker reads as `true`, and it is both a
// tuple and a `Marked`.
export function mark(xs: [number, number] & Marked): true {
  return xs[marker];
}
function sum(xs: [number, number]): number {
  return xs[0] + xs[1];
}
export function asTuple(xs: [number, number] & Marked): number {
  return sum(xs);
}
function marked(m: Marked): true {
  return m[marker];
}
export function asMarked(xs: [number, number] & Marked): true {
  return marked(xs);
}
