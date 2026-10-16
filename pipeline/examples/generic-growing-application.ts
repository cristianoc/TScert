// A generic method whose result applies its own interface at arguments that
// keep growing: Pair<number>'s push returns Pair<[number, U]>, whose push
// returns Pair<[[number, U], U']>, ... `Pair` is one equation, and an
// application is unfolded one step when a check reads it, so push is kept
// and none of those applications is enumerated.
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
export function first(p: Pair<number>): number {
  return p.first();
}
