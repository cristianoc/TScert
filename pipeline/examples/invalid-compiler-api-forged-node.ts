// A program object is no member of the family, whatever its members: no
// allocation of the program owns the marker (HOST-FAMILIES.md, "Activation"),
// so an object literal with every member `Node` states is no `Node`.
import * as ts from "typescript/unstable/ast";

export function forge(parent: ts.Node): ts.Node {
  return {
    kind: ts.SyntaxKind.Identifier,
    flags: 0,
    parent,
    pos: 0,
    end: 0,
    forEachChild: () => undefined,
    getSourceFile: () => parent.getSourceFile(),
    getStart: () => 0,
    getFullStart: () => 0,
    getEnd: () => 0,
    getWidth: () => 0,
    getFullWidth: () => 0,
    getLeadingTriviaWidth: () => 0,
    getFullText: () => "",
    getText: () => "",
  };
}
