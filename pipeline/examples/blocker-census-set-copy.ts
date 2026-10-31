// Census: type-term.mts#typeParts, #someType, #visitType, #validateAnnotation,
// #typeTerm, #readTypeTerm, #constructorForms, #mapped, #expandMapped,
// #expandIdentity, #substitute, #mapTypeParts, #tuple, #intersection,
// #signature, #quantified, #signatures, #statedResult, #statementOf,
// #promiseOf, #members, #sameIndex, #sameTerm, #sameTerms, #sameOptionalTerm,
// #sameOptionalIndex, #sameStatics, #indexKinds, #classInstance.
// Copying an optional host set before adding another element.
export function copy(scope: { aliases?: Set<string> }, alias: string): void {
  const aliases = new Set(scope.aliases ?? []);
  aliases.add(alias);
}

export function copyNumbers(
  values: Set<number> | readonly number[],
): Set<number> {
  return new Set(values);
}
