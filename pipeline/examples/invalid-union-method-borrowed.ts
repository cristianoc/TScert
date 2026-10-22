// A member of a union of hosts called on another receiver: the member's
// contract holds of its own host only, so `o.k.call(p)` promises nothing.
// Under Node, `borrowed({ tag: "a", n: 1, k() { return this.n; } },
// { tag: "b", k() { return 0; } })` returns `undefined`.
interface A {
  tag: "a";
  k(): number;
}
interface B {
  tag: "b";
  k(): number;
}

export function borrowed(o: A | B, p: A | B): number {
  return o.k.call(p);
}
