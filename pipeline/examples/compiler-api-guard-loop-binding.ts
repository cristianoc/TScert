// A family guard's test of a loop's binding: a `for...of` binding is bound
// before the body runs, so its read there cannot throw, and the guard is the
// test of the element's tag where it is held. Its false edge, reached past a
// `continue` or in an `else`, excludes the tested arm: every arm of
// `ObjectLiteralElementLike` but `SpreadAssignment` has a `name`.
import * as ts from "typescript/unstable/ast";

export function namesAfterContinue(
  o: ts.ObjectLiteralExpression,
): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const p of o.properties) {
    if (ts.isSpreadAssignment(p)) continue;
    out.push(p.name);
  }
  return out;
}

export function namesInElse(o: ts.ObjectLiteralExpression): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const p of o.properties) {
    if (ts.isSpreadAssignment(p)) {
      out.length;
    } else {
      out.push(p.name);
    }
  }
  return out;
}

export function namesOfPattern(
  entries: readonly { element: ts.ObjectLiteralElementLike }[],
): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const { element } of entries) {
    if (!ts.isSpreadAssignment(element)) out.push(element.name);
  }
  return out;
}

export function nameAfterDefault(
  p: ts.ObjectLiteralElementLike,
  fallback: string = ts.isSpreadAssignment(p) ? "" : "named",
): string {
  return fallback;
}
