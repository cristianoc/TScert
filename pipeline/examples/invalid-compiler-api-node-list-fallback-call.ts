// A method call on a node list or a fresh empty array carries its callback's
// effect: `some` calls `clear`, which writes the field the caller narrowed,
// so the field may be `undefined` after the call.
import * as ts from "typescript/unstable/ast";

export function cleared(
  n: ts.NewExpression,
  box: { v: number | undefined },
): number {
  if (box.v === undefined) return 0;
  const clear = (c: ts.Expression): boolean => {
    box.v = undefined;
    return c.pos < 0;
  };
  (n.arguments ?? []).some(clear);
  return box.v;
}
