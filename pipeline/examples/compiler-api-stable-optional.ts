// An optional member of a node's shape tested and read again past calls
// (HOST-FAMILIES.md, "Stable keys"): an optional member is fixed when the
// node is built, present with one value or absent, so the read link from
// the test's read survives every call, absent or present. `initializerOf`
// is the shape of `patternStmt` in `tools/fragment-statements.mts`: a test
// that leaves on absence, calls, and the member read as present.
import * as ts from "typescript/unstable/ast";

export function initializerOf(
  d: ts.VariableDeclaration,
  fail: (n: ts.Node) => never,
  log: (n: ts.Node) => void,
): ts.Expression {
  if (!d.initializer) fail(d);
  log(d.initializer);
  log(d);
  return d.initializer;
}

export function initializerKind(
  d: ts.VariableDeclaration,
  log: () => void,
): number {
  return d.initializer ? (log(), d.initializer.kind) : 0;
}

export function noInitializer(
  d: ts.VariableDeclaration,
  log: (n: ts.Node) => void,
): undefined {
  if (d.initializer) return undefined;
  log(d);
  return d.initializer;
}

// A corrected member, declared required and absent at run time:
// `DefaultClause.expression`, read as optional.
export function clauseExpression(
  c: ts.CaseOrDefaultClause,
  log: () => void,
): ts.Expression | null {
  if (!ts.isDefaultClause(c)) return null;
  if (!c.expression) return null;
  log();
  return c.expression;
}

// `patternStmt` of `tools/fragment-statements.mts`, reduced: a gate whose
// `fail` never returns, the member tested absent, then read past the gate's
// calls and a callback's.
const UNCLOSABLE = "an array pattern over an iterator that cannot be closed";

export class Gate {
  readonly iterations: Map<string, string> = new Map();
  fail(n: ts.Node, message: string): never {
    throw new Error(`${n.pos}: ${message}`);
  }
  span(n: ts.Node): number[] {
    return [n.pos, n.end];
  }
}

export function patternStmt(
  gate: Gate,
  list: ts.VariableDeclarationList,
  node: ts.Node,
): ts.Expression {
  if (list.declarations.length !== 1)
    gate.fail(node, "a pattern declares alone in the fragment");
  const d = list.declarations[0];
  if (!d) return gate.fail(node, "no declaration");
  if (d.type) gate.fail(d, "an annotated pattern is outside the fragment");
  if (!d.initializer) gate.fail(d, "a `const` needs an initializer");
  const kind = gate.iterations.get(gate.span(d.initializer).join(":"));
  if (ts.isArrayBindingPattern(d.name) && kind?.startsWith("client")) {
    if (
      kind === "client-unclosable" &&
      !d.name.elements.some((e) => ts.isBindingElement(e) && e.dotDotDotToken)
    )
      gate.fail(d.initializer, UNCLOSABLE);
    return d.initializer;
  }
  return d.initializer;
}
