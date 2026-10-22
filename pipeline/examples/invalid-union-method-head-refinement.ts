// A method call on a union of hosts whose actual runs code: the member is
// read and bound to the receiver before the actual, and the actual's write
// ends what the test learned of `b.v`, so returning it as a string is refused.
// Under Node, `bad({ tag: "a", m() {} }, { v: "s" })` returns `undefined`.
interface A {
  tag: "a";
  m(x: number): void;
}
interface B {
  tag: "b";
  m(x: number): void;
}
interface Box {
  v: string | undefined;
}

function clear(b: Box): number {
  b.v = undefined;
  return 0;
}

export function bad(o: A | B, b: Box): string {
  if (b.v === undefined) return "";
  o.m(clear(b));
  return b.v;
}
