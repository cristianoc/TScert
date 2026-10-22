// A method call on a union of hosts whose actual runs code: the member is
// read from the receiver and bound to it before the actual runs, so the
// actual replacing the cell's receiver leaves the call's receiver the object
// read first (JavaScript's order: the callee reference, then the arguments).
// Under Node, `first({ o: a }, b)` with `a = { tag: "a", name(n) { return "a" + n; } }`
// and `b = { tag: "b", name(n) { return "b" + n; } }` returns `"a1"`.
interface A {
  tag: "a";
  name(n: number): string;
}
interface B {
  tag: "b";
  name(n: number): string;
}
interface Cell {
  o: A | B;
}

function swap(c: Cell, other: A | B): number {
  c.o = other;
  return 1;
}

export function first(c: Cell, other: A | B): string {
  return c.o.name(swap(c, other));
}

export function local(o: A | B, other: A | B): string {
  let r = o;
  const n = (r = other).name(0).length;
  return r.name(n);
}
