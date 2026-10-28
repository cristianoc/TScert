// Unannotated callback parameters whose contexts give them standard library
// interfaces, ReadonlySet<string>, Map<string, string> and
// ReadonlyMap<string, readonly string[]>, as the parser's scopes and tables
// are: each is read as a written reference to the interface is.
// Census functions: fragment-parse.mts#lowerFile, fragment-parse.mts#parseModules.
export function bound(
  scopes: readonly ReadonlySet<string>[],
  name: string,
): boolean {
  return scopes.some((scope) => scope.has(name));
}
export function renamed(
  tables: readonly Map<string, string>[],
  name: string,
): string {
  let found = name;
  tables.forEach((table) => {
    const next = table.get(found);
    if (next !== undefined) found = next;
  });
  return found;
}
export function tagged(
  tags: readonly ReadonlyMap<string, readonly string[]>[],
  key: string,
): number {
  return tags.filter((tag) => (tag.get(key)?.length ?? 0) > 0).length;
}
