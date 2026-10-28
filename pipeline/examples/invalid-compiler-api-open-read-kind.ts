// An open read finds a numeric `kind` on `{ kind: 1 }` as on a node (run
// under Node): the read's `unknown` establishes no host family, so a guard
// promising a compiler node from it is refused.
import type { Node } from "typescript/unstable/ast";
export function isNode(value: unknown): value is Node {
  return (
    typeof value === "object" &&
    value !== null &&
    "kind" in value &&
    typeof value.kind === "number"
  );
}
