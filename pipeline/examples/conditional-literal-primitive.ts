// Rules conditional-literal and conditional-tuple-never, at the corners
// TypeScript decides: `undefined extends void`, `boolean` over `true`,
// `bigint` over a number literal, `[any] extends [never]`.
type Ex<T, U> = T extends U ? never : T;
type TN<X> = [X] extends [never] ? "T" : "F";

export function voidAbsorbsUndefined(): Ex<"a" | undefined, void> {
  return "a";
}

export function booleanSplits(): Ex<boolean, true> {
  return false;
}

export function bigintOverNumber(): Ex<1 | 2n, bigint> {
  return 1;
}

export function anyIsNotNever(): TN<any> {
  return "F";
}

export function neverIsNever(): TN<never> {
  return "T";
}
