// A spread of a program's iterable in a conditional's branch, after a test
// reading a member: JavaScript runs the test once, then the iterator's code
// in the branch the test selects, which no placement of the collection
// before the statement reproduces. The construct `visitType`
// (`tools/type-term.mts`) avoids, for these census functions:
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
type Term =
  | { readonly k: "scheme"; readonly binders: readonly string[] }
  | { readonly k: "atom" };

export function names(
  term: Term,
  bound: ReadonlySet<string>,
): ReadonlySet<string> {
  const inner =
    term.k !== "scheme" ? bound : new Set([...bound, ...term.binders]);
  return inner;
}
