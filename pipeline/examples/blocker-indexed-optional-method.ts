// An optional method of a type literal read as a type, `Scope["record"]`,
// as type-term.mts's expandMapped takes its scope's record hook.
// Census functions:
// type-term.mts#expandMapped, type-term.mts#typeTerm and 19 others of
// type-term.mts reaching it, declaration-graph.mts#libraryTerm,
// declaration-graph.mts#collect, named-record.mts#settleTerm,
// named-record.mts#settleDocument, fragment-parse.mts#lowerFile and 6
// others of fragment-parse.mts.
type Scope = { size: number; record?(key: string): number };

export function apply(get: Scope["record"], key: string): number {
  return get?.(key) ?? 0;
}
