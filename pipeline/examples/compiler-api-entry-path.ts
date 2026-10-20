// A member path of several members tested in one statement and read in a
// later one (HOST-FAMILIES.md, "Entries"): each statement entry holds a
// witness of the path and of each of its prefixes, one read link per
// segment, so the read past the statement boundary is the tested value. The
// members of a node's shapes are stable, so the chain survives a call.
import * as ts from "typescript/unstable/ast";

export function calleeText(n: ts.Node): string {
  if (!ts.isCallExpression(n) || !ts.isPropertyAccessExpression(n.expression))
    return "";
  if (!ts.isIdentifier(n.expression.expression)) return "";
  return n.expression.expression.text;
}

export function unrefinedPrefix(n: ts.CallExpression): string {
  if (!ts.isIdentifier(n.expression.parent)) return "";
  return n.expression.parent.text;
}

export function threeMembers(n: ts.PropertyAccessExpression): string {
  if (!ts.isPropertyAccessExpression(n.expression)) return "";
  if (!ts.isPropertyAccessExpression(n.expression.expression)) return "";
  if (!ts.isIdentifier(n.expression.expression.name)) return "";
  return n.expression.expression.name.text;
}

export function afterCall(n: ts.Node, log: () => void): string {
  if (!ts.isCallExpression(n) || !ts.isPropertyAccessExpression(n.expression))
    return "";
  if (!ts.isIdentifier(n.expression.expression)) return "";
  log();
  return n.expression.expression.text;
}

export function inLoop(n: ts.PropertyAccessExpression, count: number): string {
  if (!ts.isIdentifier(n.expression.parent)) return "";
  let text = "";
  for (let i = 0; i < count; i++) text = n.expression.parent.text;
  return text;
}
