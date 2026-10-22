// A guard returning a family guard's test under `&&` promises what the test
// establishes, no more: an identifier is no function declaration, so the
// filter's result holds an identifier where it promises declarations (run
// under Node).
import * as ts from "typescript/unstable/ast";

export function named(
  list: readonly ts.Node[],
  name: string,
): ts.FunctionDeclaration[] {
  return list.filter(
    (d): d is ts.FunctionDeclaration => ts.isIdentifier(d) && d.text === name,
  );
}
