// `Array.isArray` is the calculus's test of an array's identity: an array
// owns its store, which no other value does. The arm where it holds keeps
// the array parts of the tested type, and the arm where it fails the rest;
// an open record may be an array carrying other keys, so it stays on both.
type Foo = { a: string; b: number };

function length(x: number[] | string): number {
  if (Array.isArray(x)) return x.length;
  return x === "" ? 0 : 1;
}

function rest(x: number[] | Foo): Foo {
  if (Array.isArray(x)) return { a: "", b: 0 };
  return x;
}

function negated(x: [number, string] | number | null): number {
  if (!Array.isArray(x)) return x ?? 0;
  return x[0];
}

function mutable(x: number[] | boolean): void {
  if (Array.isArray(x)) x.push(1);
}

function literal(): number {
  const o = { length: 3 };
  if (Array.isArray(o)) return 0;
  return o.length;
}
