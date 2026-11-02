// Census functions:
// fragment-parse.mts#lowerModule
// fragment-parse.mts#parseModules
// fragment-parse.mts#renamedModule
// fragment-parse.mts#lowerFile
export function rename(): number | null {
  const term = (n: number): number => n;
  const param = (n: number | null): number | null => n && term(n);
  const offered: (n: number, ...more: unknown[]) => number = term;
  return param(1);
}
