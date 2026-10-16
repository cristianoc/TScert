// A constant annotated `unique symbol` and made by `Symbol()` holds a fresh
// symbol and names a key of its own, distinct from every other such
// constant's: types state fields at it, `o[k]` reads it, and `o[k] = v`
// writes it.
const tag: unique symbol = Symbol("tag");
const other: unique symbol = Symbol();
function read(o: { [tag]: number; [other]: string }): number {
  return o[tag] + o[other].length;
}
function value(): symbol {
  return tag;
}
function write(o: { [tag]: number }): void {
  o[tag] = 5;
}
export function use(o: { [tag]: number; [other]: string; n: number }): number {
  const s: symbol = value();
  write(o);
  return read(o) + o.n;
}
