// Census function: declaration-graph.mts#namesArray.
import type { TypeDefinition, ValueRoot, WrittenApplication } from "../../tools/declaration-types.mts";
import { documentHolds } from "../../tools/fragment-parts.mts";
export function namesArray(parts: { definitions: TypeDefinition[]; values: ValueRoot[]; applications: WrittenApplication[] }): boolean {
  return documentHolds({ roots: [], symbols: [], ...parts }, t => t.k === "array" || t.k === "tuple", () => false);
}
