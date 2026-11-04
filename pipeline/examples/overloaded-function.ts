// A function declared with overloads is one unit per overload: its code is
// checked at each overload's parameters and result, and a caller reads it at
// every overload. The implementation's own signature is no caller's.
// `getOr` is ReScript's at a primitive payload and at an option of one,
// whose `Some(None)` is a marker object.
type M0 = { readonly BS_PRIVATE_NESTED_SOME_NONE: 0 };
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A,
): A;
declare function valFromOption<A extends string | number | boolean | bigint>(
  x: A | M0,
): undefined | A;

export function getOr<A extends string | number | boolean | bigint>(
  o: undefined | A,
  d: A,
): A;
export function getOr<A extends string | number | boolean | bigint>(
  o: undefined | A | M0,
  d: undefined | A,
): undefined | A;
export function getOr<A extends string | number | boolean | bigint>(
  o: undefined | A | M0,
  d: undefined | A,
): undefined | A {
  if (o !== undefined) {
    return valFromOption(o);
  } else {
    return d;
  }
}
export function useFlat(o: undefined | number): number {
  return getOr(o, 3);
}
export function useNested(o: undefined | number | M0): undefined | number {
  return getOr(o, 3);
}

export function pick(x: number): number;
export function pick(x: string): string;
export function pick(x: number | string): number | string {
  return x;
}
export function count(): number {
  return pick(1);
}
export function text(): string {
  return pick("a");
}
