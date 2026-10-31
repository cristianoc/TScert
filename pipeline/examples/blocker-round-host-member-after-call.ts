// Host child text read after declaration resolution and a guard on the resolved declaration.
// Census functions:
// declaration-graph.mts#collectDeclarations
import * as ts from "typescript/unstable/ast";
import type {
  ExpressionWithTypeArguments,
  InterfaceDeclaration,
} from "typescript/unstable/ast";
import type { Checker } from "typescript/unstable/sync";
export function base(
  base: ExpressionWithTypeArguments,
  checker: Checker,
): InterfaceDeclaration {
  if (!ts.isIdentifier(base.expression) || base.typeArguments?.length)
    throw Error("identifier required");
  const targets = (
    checker.getSymbolAtLocation(base.expression)?.declarations ?? []
  ).map((x) => x.resolve());
  const [only] = targets;
  if (!only || targets.length !== 1 || !ts.isInterfaceDeclaration(only))
    throw Error(base.expression.text);
  return only;
}
