// `Array<T>` and `ReadonlyArray<T>` under Node's types, which merge the
// heritage `RelativeIndexable<T>` into both interfaces: still the array types
// `T[]` and `readonly T[]`, read as arrays, as `T[]` is.
// Census functions:
// fragment-parse.mts#lowerFile, fragment-parse.mts#lowerModule,
// fragment-parse.mts#lowerModuleText, fragment-parse.mts#parseFile,
// fragment-parse.mts#parseFragment, fragment-parse.mts#parseModules.
export function count(xs: Array<number>): number {
  return xs.length;
}

export function view(xs: number[]): ReadonlyArray<number> {
  return xs;
}

export function last(xs: ReadonlyArray<string>): string | undefined {
  return xs.at(-1);
}
