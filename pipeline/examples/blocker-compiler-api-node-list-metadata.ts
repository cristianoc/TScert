// A compiler node list's own member `pos`, read through a union of two
// lists, beside its readonly array view (COMPILER-API.md, "Node lists").
// Census functions:
// shadow-contracts.mts#rewriteSignature.
import type { FunctionDeclaration } from "typescript/unstable/ast";
export function use(node: FunctionDeclaration): number {
  return (node.typeParameters ?? node.parameters).pos;
}
