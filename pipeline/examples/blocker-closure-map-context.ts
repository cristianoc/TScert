// An unannotated callback parameter whose context gives it a library type,
// here ReadonlySet<string>, as the parser's scopes are.
// Census functions: fragment-parse.mts#lowerFile, fragment-parse.mts#parseModules.
export function bound(scopes: readonly ReadonlySet<string>[], name: string): boolean {
  return scopes.some((scope) => scope.has(name));
}
