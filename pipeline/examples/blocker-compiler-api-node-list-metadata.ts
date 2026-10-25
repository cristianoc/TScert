// A compiler node list needs its own metadata members represented beside its
// readonly array view.
// Census functions:
// shadow-contracts.mts#rewriteSignature.
import type { FunctionDeclaration } from "typescript/unstable/ast";
export function use(node: FunctionDeclaration): number {
  return (node.typeParameters ?? node.parameters).pos;
}
