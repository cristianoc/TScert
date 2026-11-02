// A recursive visitor's written growth footprint must reject shrinking the
// mapped array. Under Node, mapping two identifiers leaves a hole at index 1.
import * as ts from "typescript/unstable/ast";

export function bindings(nodes: ts.Node[]): number[] {
  const found: number[] = nodes.map((node) => {
    const reads = (
      n: ts.Node,
    ): Within<{ value: "any"; store: "grow" }, ts.Node | undefined> => {
      nodes.pop();
      if (ts.isIdentifier(n)) return n;
      return n.forEachChild(reads);
    };
    return reads(node) ? 1 : 0;
  });
  return found;
}
