// A Set constructed from another Set needs the constructor's iterable
// argument: the stated forms take an array.
// Census functions:
// computed-types.mts#aliasApplication, computed-types.mts#computedType,
// computed-types.mts#distributed, computed-types.mts#parameterMembers,
// computed-types.mts#unionMembers, fragment-expressions.mts#confined,
// fragment-expressions.mts#knownLocal.
export function copy(functions: Set<string>): Set<string> {
  return new Set<string>(functions);
}
