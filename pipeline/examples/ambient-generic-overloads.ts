// A generic function declared with overloads, each stating the same type
// parameter, is callable at each overload at every instance within its bound:
// the declaration of ReScript's `valFromOption` at a primitive payload and at
// an option of one, whose `Some(None)` is a marker object. A call is checked
// at the overload its actuals match, the instance excluding the marker.
type M0 = { readonly BS_PRIVATE_NESTED_SOME_NONE: 0 };
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A,
): A;
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A | M0,
): undefined | A;
export function flat(o: number): number {
  return valFromOption(o);
}
export function nested(o: undefined | number | M0): number {
  if (o === undefined) {
    return 0;
  }
  const n = valFromOption(o);
  if (n !== undefined) {
    return n;
  } else {
    return -1;
  }
}
export function stated(o: string | M0): undefined | string {
  return valFromOption<string>(o);
}
