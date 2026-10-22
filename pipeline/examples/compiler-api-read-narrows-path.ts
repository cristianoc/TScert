// `patternStmt`'s declaration (tools/fragment-statements.mts): the first
// declaration of a list, read by index, is narrowed by its completed read
// `d.type`; a test of `d.initializer` and a method returning `never` then
// refine the read of the path the next statement passes to `span`.
import * as ts from "typescript/unstable/ast";

class Gate {
  fail(node: ts.Node, message: string): never {
    throw new Error(`${message} at ${node.pos}`);
  }
  span(node: ts.Node): [number, number] {
    return [node.pos, node.end];
  }
}

export function initializerSpan(
  gate: Gate,
  list: ts.VariableDeclarationList,
): string {
  const d = list.declarations[0];
  if (d.type) gate.fail(d, "an annotated pattern is outside the fragment");
  if (!d.initializer) gate.fail(d, "a `const` needs an initializer");
  return gate.span(d.initializer).join(":");
}
