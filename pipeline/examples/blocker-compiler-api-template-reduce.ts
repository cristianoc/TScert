// A template's concatenation built by a reduce over its spans, each step a
// fresh record at the expression type, the substitution read by a call
// within a stated footprint.
// Census functions:
// fragment-expressions.mts#template.
import * as ts from "typescript/unstable/ast";
import type { Expression } from "typescript/unstable/ast";
type Span = [start: number, end: number];
type E =
  | { k: "lit"; pos: Span; v: string }
  | { k: "arith"; pos: Span; op: "add" | "sub"; l: E; r: E };
export function template(node: ts.TemplateExpression, f: (e: Expression) => Within<{ value: "any"; store: "grow" }, E>): Within<{ value: "any"; store: "grow" }, E> {
  const start = node.pos;
  const head: E = { k: "lit", pos: [node.head.pos, node.head.end], v: node.head.text };
  return node.templateSpans.reduce((acc: E, part): E => {
    const value: E = { k: "arith", pos: [start, part.expression.end], op: "add", l: acc, r: f(part.expression) };
    return {
      k: "arith",
      pos: [start, part.literal.end],
      op: "add",
      l: value,
      r: { k: "lit", pos: [part.literal.pos, part.literal.end], v: part.literal.text },
    };
  }, head);
}
