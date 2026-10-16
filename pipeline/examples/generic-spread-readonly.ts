// A spread of a readonly array into a generic rest reads its elements, as a
// mutable array's: the rest's binder is inferred from them.
declare function collect<T>(...args: readonly T[]): void;

export function forward<T>(values: readonly T[]): void {
  collect<T>(...values);
}

export function numbers(values: readonly number[]): void {
  collect(...values);
}
