// An optional method bound to the object it is read from, `.bind(scope)`,
// as type-term.mts's typeTerm hands its scope's record hook on.
// Census functions:
// type-term.mts#typeTerm, type-term.mts#expandMapped and 19 others of
// type-term.mts reaching typeTerm, declaration-graph.mts#collect.
type Scope = { size: number; record?(key: string): number };

export function apply(scope: Scope, key: string): number {
  const get = scope.record?.bind(scope);
  return get?.(key) ?? 0;
}
