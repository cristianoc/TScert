// The find guard overload needs to expose the promised host node type.
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
