// A node guard on a value that may be `undefined` (HOST-FAMILIES.md,
// "Undefined arguments"): every node guard of the table throws a `TypeError`
// on `undefined` before any other step, so its call tests `undefined` first,
// throws there, and is the guard's test on the rest, which both edges
// refine. A program may throw where `parent` is absent; each function here
// returns where it is present (run under Node).
import * as ts from "typescript/unstable/ast";

// The loop's test at its back edge: `at.parent` read once by the guard,
// then again, by its link, in the body.
export function outermost(n: ts.Node): ts.Node {
  let at: ts.Node = n;
  while (ts.isParenthesizedExpression(at.parent)) at = at.parent;
  return at;
}

// A path's refinement through `&&`.
export function parentNamed(n: ts.Node): boolean {
  return ts.isIdentifier(n.parent) && n.parent.text === "x";
}

// A local bound from `parent`, tested by name.
export function parentText(n: ts.Node): string {
  const p = n.parent;
  if (ts.isIdentifier(p)) return p.text;
  return "";
}

// The false edge: the guard threw where `parent` was absent, so it holds a
// node there.
export function parentKind(n: ts.Node): ts.SyntaxKind {
  if (!ts.isIdentifier(n.parent)) return n.parent.kind;
  return n.parent.kind;
}

// The thrown `TypeError` caught, its handler refining nothing.
export function caught(n: ts.Node): boolean {
  try {
    return ts.isIdentifier(n.parent);
  } catch {
    return false;
  }
}

// The operand evaluated once: `counted` returns 1.
const calls = { count: 0 };

function next(n: ts.Node): ts.Node {
  calls.count += 1;
  return n;
}

export function counted(n: ts.Node): number {
  const before = calls.count;
  ts.isIdentifier(next(n).parent);
  return calls.count - before;
}

// In a callback's body.
export function namedParents(nodes: readonly ts.Node[]): ts.Node[] {
  return nodes.filter((m) => ts.isIdentifier(m.parent));
}

// The handler of the throw reads `parent` at its declared type.
export function handlerParent(n: ts.Node): ts.Node | undefined {
  try {
    return ts.isIdentifier(n.parent) ? n : undefined;
  } catch {
    return n.parent;
  }
}
