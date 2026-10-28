// `Object.entries` of an `object`: TypeScript selects the generic overload at
// the array arm and the plain one at `{}` at the other, which are one callee.
// An `object` admits a compiler object, whose own fields the plain overload
// would hand to the program, and its array arm a node list: the call is
// refused at the overload's non-host parameter (R8, COMPILER-API.md).
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
  return Array.isArray(o) ? Object.entries(o) : Object.entries(o);
}
