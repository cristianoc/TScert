// Census: type-term.mts#typeParts, #someType, #visitType, #validateAnnotation,
// #typeTerm, #readTypeTerm, #constructorForms, #mapped, #expandMapped,
// #expandIdentity, #substitute, #mapTypeParts, #tuple, #intersection,
// #signature, #quantified, #signatures, #statedResult, #statementOf,
// #promiseOf, #members, #sameIndex, #sameTerm, #sameTerms, #sameOptionalTerm,
// #sameOptionalIndex, #sameStatics, #indexKinds, #classInstance.
// Copying an optional readonly set before adding another element.
export function copy(
  scope: { aliases?: ReadonlySet<string> },
  alias: string,
): void {
  const aliases = new Set(scope.aliases ?? []);
  aliases.add(alias);
}
