// A generic alias TypeScript computes from its parameters, `T[number]` or
// `keyof T`, has no equation over them: each application is the computed
// type at its arguments, evaluated where it is written, through other such
// aliases, generic aliases of arrays and intersections of arrays.
type ElementOf<T extends readonly unknown[]> = T[number];
type Keys<T> = keyof T;
type List<E> = readonly E[];
type Item<E> = List<E>[number];
type Nested<E> = Item<List<E>>;
type Both<T> = (readonly T[] & readonly T[])[number];
declare function first<E>(xs: List<E>): Item<E>;
declare function firstList<E>(xs: readonly List<E>[]): Nested<E>;
declare function pick<T>(xs: readonly T[]): Both<T>;
function element<E>(xs: readonly E[]): ElementOf<readonly E[]> | undefined {
  return xs[0];
}
function concrete(xs: readonly number[]): ElementOf<readonly number[]> {
  return xs[0] ?? 0;
}
function key<E>(x: { good: E }): Keys<{ good: E }> {
  return "good";
}
export function use(
  xs: readonly number[],
  ys: readonly (readonly string[])[],
): number {
  const n: number = first(xs);
  const s: readonly string[] = firstList(ys);
  const m: number = pick(xs);
  return (
    n +
    s.length +
    m +
    concrete(xs) +
    (element(xs) ?? 0) +
    key({ good: 1 }).length
  );
}
