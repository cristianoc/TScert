// Census functions: fragment-statements.mts#declarationsOf,#statements.
// A recursive visitor inside map must preserve the receiver's array stores.
import * as ts from "typescript/unstable/ast";
type Gate = {
  local: (n: ts.Identifier) => Within<{ value: "keep"; store: "keep" }, string>;
};
export function bindings(nodes: ts.Node[], gate: Gate): number[] {
  const found: number[] = nodes.map((node) => {
    const reads = (n: ts.Node): ts.Node | undefined => {
      if (ts.isIdentifier(n) && gate.local(n) === "self") return n;
      return n.forEachChild(reads);
    };
    return reads(node) ? 1 : 0;
  });
  return found;
}
