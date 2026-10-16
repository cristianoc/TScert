// A function type met with a record of writable fields is the function
// carrying those fields: TypeScript's record type holds such functions too.
// So is an interface with a call signature extending a record, and an
// interface stating no member of its own is its bases' meet.
interface Named {
  a: number;
}
interface Counter extends Named {
  (): void;
}
interface Callback extends Function {}
type Empty = {};
interface ViaEmpty extends Empty {
  readonly e: number;
}
function viaEmpty(i: ViaEmpty): number {
  return i.e;
}
function call(h: (() => void) & { a: number }): number {
  h();
  return h.a;
}
function count(c: Counter): number {
  c();
  return c.a;
}
function callback(g: () => number): Callback {
  return g;
}
export function use(h: (() => void) & Named, c: Counter): number {
  callback(() => 1);
  return call(h) + count(c) + viaEmpty({ e: 1 });
}
