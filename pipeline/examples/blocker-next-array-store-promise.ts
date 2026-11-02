// Census: type-term.mts#typeParts, #someType, #visitType, #validateAnnotation,
// #typeTerm, #readTypeTerm, #constructorForms, #mapped, #expandMapped,
// #expandIdentity, #substitute, #mapTypeParts, #tuple, #intersection,
// #signature, #quantified, #signatures, #statedResult, #statementOf,
// #promiseOf, #members, #sameIndex, #sameTerm, #sameTerms, #sameOptionalTerm,
// #sameOptionalIndex, #sameStatics, #indexKinds, #classInstance.
interface Term {
  kind: string;
}
export function settled(values: (Term | null)[]): boolean {
  return values.every((v) => v !== null);
}
