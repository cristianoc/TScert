// Generic bodies the graph checker certifies, each binder read as a parameter
// row: records, tuples and arrays over a binder, field reads and writes, and
// literals, `??`, `if`, `let` and `typeof` beside it.
type Box<T> = { value: T };

function get<T>(b: Box<T>): T {
  return b.value;
}
function make<T>(x: T): Box<T> {
  return { value: x };
}
function set<T>(b: Box<T>, x: T): void {
  b.value = x;
}
function swap<T>(a: Box<T>, b: Box<T>): void {
  const saved = a.value;
  a.value = b.value;
  b.value = saved;
}
function pair<T, U>(x: T, y: U): [T, U] {
  return [x, y];
}
function first<T>(xs: T[]): T | undefined {
  return xs[0];
}
function pick<T>(x: T, b: boolean): T | number {
  if (b) {
    return 1;
  }
  return x;
}
function fallback<T>(x: T | null, y: T): T {
  return x ?? y;
}
function kind<T>(x: T): string {
  if (typeof x === "string") {
    return "s";
  }
  let n = 0;
  n = n + 1;
  return "o";
}
function boxed<T>(x: T): T {
  return get(make(x));
}

export function callers(n: number): number {
  const b = make(n);
  set(b, 2);
  return get(b) + boxed(n);
}
