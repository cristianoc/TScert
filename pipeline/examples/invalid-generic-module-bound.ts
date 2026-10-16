// A call cannot instantiate a binder beyond its bound.
function atMost<T extends boolean>(x: T): boolean {
  return x;
}
export function overBound(n: number): boolean {
  return atMost(n);
}
