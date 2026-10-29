// The array form of `getSymbolAtLocation` gives one entry per node, each a
// `Symbol` or `undefined`: a node with no symbol (a statement) gives
// `undefined`, which `!` does not rule out (run under Node).
import type { Node } from "typescript/unstable/ast";
import type { Checker, Symbol } from "typescript/unstable/sync";

export function wrong(checker: Checker, nodes: readonly Node[]): Symbol {
  return checker.getSymbolAtLocation(nodes)[0]!;
}
