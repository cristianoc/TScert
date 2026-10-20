// A member path a test refined, read again past a call (HOST-FAMILIES.md,
// "Stable links"): the members of a node's shapes are stable, so the read
// link from the test's read survives the call, and the later read is the
// tested value. The calls run code the checker knows nothing of: an
// unrelated one, an external one receiving the node, and a write of a
// program record between the test and the read.
import * as ts from "typescript/unstable/ast";

export function operandText(node: ts.Node, log: (n: ts.Node) => void): string {
  if (ts.isPrefixUnaryExpression(node) && ts.isIdentifier(node.operand)) {
    log(node);
    return node.operand.text;
  }
  return "";
}

export function nameText(m: ts.Node, log: () => void): string {
  if (!ts.isPropertyAssignment(m)) return "";
  if (!ts.isIdentifier(m.name)) return "";
  log();
  return m.name.text;
}

export function countedText(m: ts.Node, box: { count: number }): string {
  if (!ts.isPropertyAssignment(m)) return "";
  if (!ts.isIdentifier(m.name)) return "";
  box.count = box.count + 1;
  return m.name.text;
}
