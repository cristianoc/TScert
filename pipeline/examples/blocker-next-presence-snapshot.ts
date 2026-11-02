// Census functions: claim-text.mts#atomText, #bareAtomText, #typeText, #printType,
// #liftClause, #liftSignatures, #liftType, #liftLabels, #treeAtom, #lift.
import type { JsonObject } from "../../tools/calculus.mts";
import { isArrayPresence, presencePrefix } from "../../tools/type-graph.mts";
export function print(atom: JsonObject): string {
  const presence = atom.presence;
  return isArrayPresence(presence) ? presencePrefix(presence) : "invalid";
}
