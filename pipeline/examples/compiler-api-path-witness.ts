import * as ts from "typescript/unstable/ast";

export function guard(m: ts.PropertyAssignment): string {
  return ts.isIdentifier(m.name) ? m.name.text : "";
}

export function kind(m: ts.PropertyAssignment): string {
  return m.name.kind === ts.SyntaxKind.Identifier ? m.name.text : "";
}

export function logical(m: ts.PropertyAssignment): string | false {
  return ts.isIdentifier(m.name) && m.name.text;
}

export function either(m: ts.PropertyAssignment): string {
  return ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)
    ? m.name.text
    : "";
}

export function split(m: ts.PropertyAssignment): string {
  if (ts.isIdentifier(m.name)) return m.name.text;
  return "";
}

export function nested(h: { readonly node: ts.PropertyAssignment }): string {
  return ts.isIdentifier(h.node.name) ? h.node.name.text : "";
}

export function consume(n: ts.Node): number {
  return n.pos;
}

export function broad(m: ts.PropertyAssignment): number {
  return ts.isIdentifier(m.name) ? consume(m.name) : 0;
}

export function parent(holder: ts.Node): ts.Node {
  return holder.parent ? consumeParent(holder.parent) : holder;
}

function consumeParent(n: ts.Node): ts.Node {
  return n;
}

export function skipped(flag: boolean, m: ts.PropertyAssignment): string {
  return flag && ts.isIdentifier(m.name) ? m.name.text : "";
}

export function defaulted(
  m: ts.PropertyAssignment,
  text: string = ts.isIdentifier(m.name) ? m.name.text : "",
): string {
  return text;
}

export function patternDefault(
  m: ts.PropertyAssignment,
  input: { text?: string },
): string {
  const { text = ts.isIdentifier(m.name) ? m.name.text : "" } = input;
  return text;
}

export function deepTruthy(holder: { readonly node: ts.Node }): number {
  return holder.node.parent ? holder.node.parent.pos : 0;
}

export function afterTest(m: ts.PropertyAssignment): string {
  if (!ts.isIdentifier(m.name)) return "";
  return m.name.text;
}
