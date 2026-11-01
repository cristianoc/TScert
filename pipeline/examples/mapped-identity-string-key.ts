// Census: tools/type-term.mts#expandIdentity and its callers, including typeParts.
// The collected mapped-type keys are strings; the symbol-record arm of the
// property-key encoding is outside this collection's domain.
function describe(key: string): string[] {
  const names: string[] = [];
  names.push(key);
  return names.map((n) => String(n));
}
