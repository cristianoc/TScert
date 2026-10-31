// The optional structural ReadonlySet may have a client-defined iterator.
// The empty-array fallback supplies no provenance for the other arm.
export function copy(scope: { aliases?: ReadonlySet<string> }): Set<string> {
  return new Set<string>(scope.aliases ?? []);
}
