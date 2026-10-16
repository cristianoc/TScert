// An array is an Iterable of its elements: `Array.prototype[Symbol.iterator]`
// iterates the store of the array it is invoked on. A literal expected as an
// Iterable is a readonly array of the type the Iterable yields.
export function iterate(xs: readonly number[]): Iterable<number> {
  return xs;
}

export function pairs(key: string, n: number): Iterable<[string, number]> {
  return [[key, n]];
}
