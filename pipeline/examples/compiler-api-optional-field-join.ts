// A test of a compiler node's optional field, then a call that may change
// any value in each branch, then the branches' join: the join's entry
// asserts the field at its declared type, which the declared read
// establishes, and no entry the flow reaches from it reads the field
// through the test's link, so the join keeps no witness of the path and
// the edges after the calls carry no link (HOST-FAMILIES.md, "Entries").
// `rest` is the form of the census functions
// fragment-statements.mts#pattern, #letPatternOf and #forOfPattern.
import * as ts from "typescript/unstable/ast";

export function spread(el: ts.BindingElement, out: number[]): number {
  if (el.dotDotDotToken) out.push(1);
  else out.push(2);
  return out.length;
}

export function rest(
  elements: readonly ts.ArrayBindingElement[],
  out: number[],
): void {
  elements.forEach((el) => {
    if (ts.isOmittedExpression(el) || !el.name) return;
    if (el.dotDotDotToken) out.push(el.name.kind);
    else out.push(el.name.kind + 1);
  });
}
