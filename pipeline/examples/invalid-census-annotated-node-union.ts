import type {
  ClassDeclaration,
  InterfaceDeclaration,
  Node,
} from "typescript/unstable/ast";

export function contains(
  part: ClassDeclaration | InterfaceDeclaration,
  text: string,
): boolean {
  return part.members.some((m: Node): boolean =>
    m.getText(part.getSourceFile()).trim(),
  );
}
