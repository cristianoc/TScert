// An alias application inside `Extract` keeps its bound: `B<number>` violates
// `T extends string`, as it would outside a conditional type.
interface R {
  x: number;
}
type B<T extends string> = R;
export function f(x: Extract<B<number>, unknown>): Extract<B<number>, unknown> {
  return x;
}
