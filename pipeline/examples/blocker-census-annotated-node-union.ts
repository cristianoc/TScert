// Census function: declaration-graph.mts#collect.
// An annotated callback on the union of class and interface member arrays.
import type {
  ClassDeclaration,
  InterfaceDeclaration,
  Node,
} from "typescript/unstable/ast";

export function contains(
  part: ClassDeclaration | InterfaceDeclaration,
  text: string,
): boolean {
  return part.members.some(
    (m: Node) => m.getText(part.getSourceFile()).trim() === text,
  );
}
