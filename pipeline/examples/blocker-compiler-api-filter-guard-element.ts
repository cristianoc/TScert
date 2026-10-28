// An element of a node list filtered by a compiler guard needs the guard's
// node type, whose members it reads.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
import * as ts from "typescript/unstable/ast";
export function arity(node: ts.ClassDeclaration): number {
  const constructors = node.members.filter(ts.isConstructorDeclaration);
  const constructor = constructors[0];
  return constructor ? constructor.parameters.length : 0;
}
