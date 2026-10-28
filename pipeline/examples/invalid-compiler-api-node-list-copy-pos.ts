// A spread copy's own fields contain only the array's elements and length.
import type { FunctionDeclaration } from "typescript/unstable/ast";

export function position(n: FunctionDeclaration): number {
  return [...n.parameters].pos;
}
