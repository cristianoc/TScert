// A listed guard binds only through its entry point's specifier, whose
// export Node loads as the checked function (HOST-FAMILIES.md, "Calls").
// TypeScript reads `typescript/unstable/other` at the guard's declaration,
// but Node may load other code for it: `n` stays a node, refused at
// `n.text`. Under Node, with a package whose `./unstable/other` exports a
// function answering `true` of every node, `name` returns `undefined`.
import { isIdentifier } from "typescript/unstable/other";
import type { Node } from "typescript/unstable/ast";

export function name(n: Node): string {
  return isIdentifier(n) ? n.text : "";
}
