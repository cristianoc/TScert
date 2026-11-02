// Census functions:
// strip-types.mts#stripTypes
import * as nodeModule from "node:module";
export function stripper(): unknown {
  return nodeModule.stripTypeScriptTypes;
}

export function erase(source: string): string {
  const available: unknown = nodeModule.stripTypeScriptTypes;
  if (typeof available !== "function")
    throw Error("this runtime cannot erase type annotations");
  return String(nodeModule.stripTypeScriptTypes(source));
}
