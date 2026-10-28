// Generic argument spread passes the node list's elements.
import type { FunctionDeclaration } from "typescript/unstable/ast";

function count<T>(...xs: T[]): number {
  return xs.length;
}

export function arity(n: FunctionDeclaration): number {
  return count(...n.parameters);
}
