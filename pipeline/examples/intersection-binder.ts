// An intersection with a type parameter is a meet row: the binder's parameter
// row within the other operands, below each of them, and at an instance the
// meet of the instance with them.
interface A {
  a: number;
}
function pick<T>(x: T & A): T {
  return x;
}
function field<T>(x: T & A): number {
  return x.a;
}
function second<T, U>(t: T, both: T & U): U {
  return both;
}
function tag<T>(x: T, y: T & "fixed"): T {
  return x;
}
export function use(): number {
  const x: { a: number } = pick({ a: 1 });
  return (
    x.a + field({ a: 2 }) + second("a", "b").length + tag("hi", "fixed").length
  );
}
