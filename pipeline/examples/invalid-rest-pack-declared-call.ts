// At `T = readonly number[]` the rest's argument lists are lists of numbers:
// a string is no number.
declare function factory<T extends readonly unknown[]>(
  seed: T,
): (...args: T) => void;

export function wrong(values: readonly number[]): void {
  const call = factory(values);
  // @ts-expect-error: a string is no number
  call("wrong");
}
