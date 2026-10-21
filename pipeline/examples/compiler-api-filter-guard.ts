// `filter` at a guard closure over compiler nodes, as the front end's
// `readCannotThrow` reads a scope's function declarations: the result is the
// promise's type, and the closures over it read their parameter there.
import * as ts from "typescript/unstable/ast";

export function definedFunction(statements: readonly ts.Statement[]): boolean {
  const named = statements.filter((d): d is ts.FunctionDeclaration =>
    ts.isFunctionDeclaration(d),
  );
  return (
    named.some((d) => !!d.body) &&
    !named.some((d) =>
      d.modifiers?.some((m) => m.kind === ts.SyntaxKind.DeclareKeyword),
    )
  );
}
