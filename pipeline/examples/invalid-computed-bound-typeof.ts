// A `typeof` alias keeps its bound, though its equation names no parameter.
const box = { a: 1 };
type BoxOf<T extends string> = typeof box;
export function f(x: BoxOf<number>): { a: number } {
  return x;
}
