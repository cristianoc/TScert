// Census function: intrinsics.mts#instanceOfCollection.
// The native collection guard adds a promise to the preserving effect.
import type { TypeTerm } from "../../tools/declaration-types.mts";
import { emptyEffect } from "../../tools/type-graph.mts";
type Signature = Extract<TypeTerm, { k: "function" }>;
export function collection(view: TypeTerm): TypeTerm {
  const plain: Signature = { k: "function", effect: emptyEffect, receiver: null,
    params: [{ k: "atom", name: "unknown", span: [0, 0] }], rest: null,
    result: { k: "atom", name: "boolean", span: [0, 0] }, span: [0, 0] };
  return { k: "intersection", span: [0, 0], parts: [plain,
    { ...plain, effect: { ...emptyEffect, promise: { guards: { param: 0 } } }, result: view }] };
}
