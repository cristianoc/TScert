// A recursive generic alias applied to a binder is its application row at the
// binder's parameter row: the equation is lowered once, not unrolled.
type List<T> = null | { head: T; tail: List<T> };

function push<T>(x: T, xs: List<T>): List<T> {
  return { head: x, tail: xs };
}
function build<T>(x: T, y: T): List<T> {
  let result: List<T> = null;
  result = { head: x, tail: result };
  result = { head: y, tail: result };
  return result;
}
function head<T>(xs: { head: T; tail: List<T> }): T {
  return xs.head;
}
function nested<T>(x: List<T>, y: List<List<T>>): List<List<T>> {
  return { head: x, tail: y };
}
export function numbers(n: number): number {
  return head({ head: n, tail: push(n, null) });
}
