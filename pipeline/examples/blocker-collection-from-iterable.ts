// A Set constructed from another Set, and a Map from another Map: the
// iterable overloads are stated at a host collection's reading view, whose
// iteration is the host's, and the copy is a fresh collection.
// Census functions:
// computed-types.mts#aliasApplication, computed-types.mts#computedType,
// computed-types.mts#distributed, computed-types.mts#parameterMembers,
// computed-types.mts#unionMembers, fragment-expressions.mts#confined,
// fragment-expressions.mts#knownLocal.
export function copy(functions: Set<string>): Set<string> {
  return new Set<string>(functions);
}

export function copied(members: Map<string, number>): Map<string, number> {
  const fresh = new Map(members);
  fresh.set("added", 1);
  return fresh;
}

export function grown(seen: Set<number>): number {
  const targets = new Set(seen);
  targets.add(seen.size);
  return targets.size - seen.size;
}
