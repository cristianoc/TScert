// Explicit type arguments on plain calls state the instance each call is
// typed at: a module function at a wider instance than inference would pick,
// a declared function at the instance a bound admits, dependent bounds, and a
// local quantified closure.
function same<T>(x: T): T {
  return x;
}
declare function pick<V extends string>(): V;
declare function dependent<A, B extends A>(): B;

export function widened(n: number): number | boolean {
  return same<number | boolean>(n);
}
export function literal(): string {
  return pick<"hello">();
}
export function chained(): number {
  return dependent<number, 42>();
}
export function local(flag: boolean): boolean {
  const id = <T>(x: T): T => x;
  return id<boolean>(flag);
}
