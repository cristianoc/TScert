// A listed guard's call of any argument but an immutable name is an ordinary
// call at its entry's signature (HOST-FAMILIES.md, "Calls"): its argument is
// evaluated once, so `counted` returns 1 (run under Node).
import * as ts from "typescript/unstable/ast";

const calls = { count: 0 };

function next(n: ts.Node): ts.Node {
  calls.count += 1;
  return n;
}

export function counted(n: ts.Node): number {
  const before = calls.count;
  ts.isIdentifier(next(n));
  return calls.count - before;
}
