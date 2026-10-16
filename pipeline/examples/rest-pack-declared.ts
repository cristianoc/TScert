// Declared generic functions whose rest is typed by a type parameter. A
// parameter only the rest uses is an argument pack; one typing a value too is
// instantiated at an array or tuple type, the rest's argument lists being
// that type's.
type Safe = string | number | object;
declare function emptyInfer<T extends readonly unknown[]>(...args: T): T;
declare function inferTuple<Params extends readonly Safe[]>(
  ...args: Params
): Params;
declare function factory<T extends readonly unknown[]>(
  seed: T,
): (...args: T) => void;
declare function count<T extends readonly number[]>(...args: T): number;

export function empty(): readonly unknown[] {
  return emptyInfer();
}

export function tuple(): readonly [string, number] {
  return inferTuple("a", 1);
}

export function outer(values: readonly number[]): void {
  const call = factory(values);
  call(1, 2, 3);
  call();
}

export function packed(): number {
  return count(1, 2) + count();
}

// A spread of a tuple of required positions is its positions, read as the
// call's actuals: the instance is the tuple of all of them.
export function spreads(
  pair: [number, number],
  fixed: readonly [string, number],
): number {
  const t: readonly [string, number] = inferTuple(...fixed);
  return count(...pair) + count(1, ...pair) + t[1];
}
