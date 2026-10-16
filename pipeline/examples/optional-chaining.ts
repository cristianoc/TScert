// Optional chaining: the receiver once, `undefined` where it is null or
// undefined, else the rest of the chain on its value; a later `?.` tests the
// chain so far. A method called through the chain has the present receiver.
interface Box {
  f: number;
  inner: { g: string } | null;
}
function readF(x: Box | undefined): number | undefined {
  return x?.f;
}
function deep(x: Box | null): string | undefined {
  return x?.inner?.g;
}
function chained(x: { a: { b: number } } | undefined): number | undefined {
  return x?.a.b;
}
function callIt(f: ((n: number) => number) | undefined): number | undefined {
  return f?.(1);
}
function element(xs: number[] | undefined): number | undefined {
  return xs?.[0];
}
interface Counter {
  count: number;
  next: (this: Counter) => number;
}
function invokeIt(o: Counter | null): number | undefined {
  return o?.next();
}
function present(x: Box): number {
  return x?.f;
}
function nothing(): undefined {
  return null?.toString();
}
