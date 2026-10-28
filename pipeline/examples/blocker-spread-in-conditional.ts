// A spread of a program's iterable in a conditional's branch needs its
// iterator placed after the test, which runs no code.
// Census functions:
// type-term.mts#classInstance, type-term.mts#constructorForms,
// type-term.mts#expandIdentity, type-term.mts#expandMapped,
// type-term.mts#indexKinds, type-term.mts#intersection, type-term.mts#mapped,
// type-term.mts#mapTypeParts, type-term.mts#members, type-term.mts#overloadTerm,
// type-term.mts#promiseOf, type-term.mts#quantified, type-term.mts#readTypeTerm,
// type-term.mts#sameIndex, type-term.mts#sameOptionalIndex,
// type-term.mts#sameOptionalTerm, type-term.mts#sameStatics,
// type-term.mts#sameTerm, type-term.mts#sameTerms, type-term.mts#signature,
// type-term.mts#signatures, type-term.mts#someType, type-term.mts#statedResult,
// type-term.mts#statementOf, type-term.mts#substitute, type-term.mts#tuple,
// type-term.mts#typeParts, type-term.mts#typeTerm,
// type-term.mts#validateAnnotation, type-term.mts#visitType.
export function names(
  k: string,
  bound: ReadonlySet<string>,
  more: readonly string[],
): ReadonlySet<string> {
  const inner = k !== "scheme" ? bound : new Set([...bound, ...more]);
  return inner;
}
