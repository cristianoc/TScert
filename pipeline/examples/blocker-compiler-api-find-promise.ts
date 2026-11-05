// The find guard overload gives the promised host node type, or `undefined`.
// Census functions:
// computed-types.mts#unionMembers, fragment-classes.mts#selfConstruction,
// fragment-classes.mts#staticPrivate,
// fragment-expressions.mts#hasInstanceAlong,
// fragment-expressions.mts#hasInstanceClass.
import * as ts from "typescript/unstable/ast";
export function use(file: ts.SourceFile): number {
  const declaration = file.statements.find((st): st is ts.ClassDeclaration =>
    ts.isClassDeclaration(st),
  );
  return declaration ? declaration.members.length : 0;
}
