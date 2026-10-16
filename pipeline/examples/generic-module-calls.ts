// A generic module function, certified for every instantiation, called from
// other functions at the types each call names, including at two types in
// one body, and through a bound.
function same<T>(x: T): T {
  return x;
}
function atMost<T extends boolean>(x: T): boolean {
  return x;
}
export function both(flag: boolean, n: number): number {
  const kept = same(flag);
  return kept ? same(n) : n;
}
export function bounded(flag: true): boolean {
  return atMost(flag);
}
