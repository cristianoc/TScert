// The binder is inferred from the spread array's elements, strings: the
// call's value is no number.
declare function first<T>(...args: readonly T[]): T;

export function forward(values: readonly string[]): number {
  return first(...values);
}
