// A call of a generic function declared with overloads has the result of
// the overload its actuals match: at a marker, `valFromOption` gives
// `undefined | A`, never the first overload's `A`.
type M0 = { readonly BS_PRIVATE_NESTED_SOME_NONE: 0 };
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A,
): A;
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A | M0,
): undefined | A;
export function wrong(o: number | M0): number {
  return valFromOption(o);
}
