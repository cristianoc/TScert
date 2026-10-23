// A disjunction of family guards whose left operand reads a member of the
// node it tested (`fragment-statements.mts#inert`): on the path where the
// left guard answered `true` and its member test `false`, the saved read of
// the node stays at the left guard's arm while the right guard tests the
// node again. The right guard's answers leave each slot holding the node at
// its own slice: on its true edge none (the path is never taken), on its
// false edge the left guard's arm.
import * as ts from "typescript/unstable/ast";

export function plain(p: ts.ObjectLiteralElementLike): boolean {
  return ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer ||
    ts.isPropertyAssignment(p) && !ts.isComputedPropertyName(p.name);
}

export function tested(p: ts.ObjectLiteralElementLike): boolean {
  if (ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer ||
    ts.isPropertyAssignment(p) && !ts.isComputedPropertyName(p.name)) return true;
  return false;
}

export function kindRead(p: ts.ObjectLiteralElementLike): boolean {
  return ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer ||
    ts.isPropertyAssignment(p) && p.name.kind === ts.SyntaxKind.Identifier;
}

export function saved(p: ts.ObjectLiteralElementLike): boolean {
  const q = p;
  return ts.isShorthandPropertyAssignment(q) && !q.objectAssignmentInitializer ||
    ts.isPropertyAssignment(p) && ts.isIdentifier(p.name);
}
