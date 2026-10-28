// Erasure preserves the key capability: a node's internal view is not audited.
import type { Node } from "typescript/unstable/ast";

function expose(x: unknown): unknown {
  return typeof x === "object" && x !== null && "view" in x
    ? x.view
    : undefined;
}

export function internal(node: Node): unknown {
  return expose(node);
}
