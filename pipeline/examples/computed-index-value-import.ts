// An indexed access into an imported union alias is the union of each
// member's declared type at the key, as for a local alias: `Shape["at"]` is
// the pair both members state, and `Shape["kind"]` the two literals.
// Census functions: declaration-graph.mts#libraryTerm (through
// compiler-api.mts#nodeListMembers, `TypeTerm["span"]`).
import type { Shape } from "@fixture/lib";
export function x(at: Shape["at"]): number {
  return at[0];
}
export function name(kind: Shape["kind"]): string {
  return kind;
}
