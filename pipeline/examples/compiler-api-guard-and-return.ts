// A family guard's call is a test of its argument's tags, a Boolean by its
// form: a type guard returning it under `&&` or `||` returns its truth, so
// the promise is checked where the test answers `true` (SOURCE-ELABORATION.md,
// "Derived source forms"), in an arrow's expression body and in a `return`.
import * as ts from "typescript/unstable/ast";

export function named(
  list: readonly ts.Statement[],
  name: string,
): ts.FunctionDeclaration[] {
  return list.filter(
    (d): d is ts.FunctionDeclaration =>
      ts.isFunctionDeclaration(d) && d.name?.text === name,
  );
}

export function isNamedClass(node: ts.Node): node is ts.ClassDeclaration {
  return ts.isClassDeclaration(node) && node.name !== undefined;
}

export function isFunctionOrTrue(node: ts.Node, all: boolean): boolean {
  return all || ts.isFunctionDeclaration(node);
}
