// A guard binds by what Node loads for the import (HOST-FAMILIES.md, "Calls"):
// TypeScript reads `./compiler-api-guard-mismatch-reexport.js` as the `.ts`
// module re-exporting `isIdentifier`, while Node loads the `.js` file beside
// it, other code. `n` stays a node, refused at `n.text`; under Node `name`
// returns `undefined` on a node of no text.
import { isIdentifier } from "./compiler-api-guard-mismatch-reexport.js";
import type { Node } from "typescript/unstable/ast";

export function name(n: Node): string {
  return isIdentifier(n) ? n.text : "";
}
