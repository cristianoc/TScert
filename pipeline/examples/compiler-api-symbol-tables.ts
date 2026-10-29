// A symbol's member and export tables, `Symbol.getMembers` and `getExports`
// of the compiler-API contract's view (COMPILER-API.md, "Audits of sync
// members"), read as `declaration-graph.mts#collectDeclarations` reads them
// in `exportsOf`: iterated by their entries, each key a string the
// package produced, each value a host `Symbol`.
import {
  SymbolFlags,
  type Checker,
  type Symbol,
} from "typescript/unstable/sync";

export function exportsOf(checker: Checker, symbol: Symbol): Symbol[] {
  const found = new Map<number, Symbol>();
  if (symbol.flags & (SymbolFlags.ValueModule | SymbolFlags.NamespaceModule)) {
    for (const e of checker.getExportsOfModule(symbol)) found.set(e.id, e);
    for (const [key, e] of symbol.getExports())
      if (key === "export=" || key === "default") found.set(e.id, e);
  }
  if (symbol.flags & SymbolFlags.Class) {
    for (const [, e] of symbol.getMembers()) found.set(e.id, e);
    for (const [key, e] of symbol.getExports())
      if (key !== "prototype") found.set(e.id, e);
  }
  return [...found.values()];
}

// A table read at a string the client holds: `get` and `has`, the standard
// `Map` methods, take any key, and a key the table lacks reads nothing.
export function defaultExport(symbol: Symbol): Symbol | undefined {
  const exports = symbol.getExports();
  return exports.has("default")
    ? exports.get("default")
    : exports.size > 0
      ? exports.get("export=")
      : undefined;
}
