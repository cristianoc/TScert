// An annotation written Array<T>, which reads the standard library's
// declaration of Array, where T[] does not.
// Census functions:
// fragment-parse.mts#lowerFile, fragment-parse.mts#lowerModule,
// fragment-parse.mts#lowerModuleText, fragment-parse.mts#parseFile,
// fragment-parse.mts#parseFragment, fragment-parse.mts#parseModules,
// fragment-parse.mts#diagnosticFragment.
export function count(xs: Array<number>): number {
  return xs.length;
}
