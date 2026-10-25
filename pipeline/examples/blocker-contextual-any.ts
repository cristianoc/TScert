// A callback context typed any states no contract (SOURCE-FRAGMENT, Functions,
// calls and methods).
// Census functions:
// type-term.mts#classInstance, type-term.mts#constructorForms,
// type-term.mts#expandMapped, type-term.mts#indexKinds,
// type-term.mts#intersection, type-term.mts#mapped, type-term.mts#members,
// type-term.mts#promiseOf, type-term.mts#quantified,
// type-term.mts#readTypeTerm, type-term.mts#sameData, type-term.mts#sameIndex,
// type-term.mts#signature, type-term.mts#signatures,
// type-term.mts#statedResult, type-term.mts#statementOf,
// type-term.mts#substitute, type-term.mts#tuple, type-term.mts#typeTerm,
// type-term.mts#validateAnnotation, type-term.mts#visitType.
export function use(o: object): [string, unknown][] {
  return Object.entries(o).filter(
    ([key, value]) => key !== "span" && value !== undefined,
  );
}
