// An element of a node list filtered by a compiler guard, or found by one,
// is at the guard's node type, whose members it reads.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
import * as ts from "typescript/unstable/ast";
export function arity(node: ts.ClassDeclaration): number {
  const constructors = node.members.filter(ts.isConstructorDeclaration);
  const constructor = constructors[0];
  return constructor ? constructor.parameters.length : 0;
}

export function found(node: ts.ClassDeclaration): number {
  const constructor = node.members.find(ts.isConstructorDeclaration);
  return constructor ? constructor.parameters.length : 0;
}
