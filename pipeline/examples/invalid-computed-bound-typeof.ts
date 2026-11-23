// A `typeof` alias keeps its bound.
const box = { a: 1 };
type BoxOf<T extends string> = typeof box | T;
export function f(x: BoxOf<number>): BoxOf<number> {
  return x;
}
