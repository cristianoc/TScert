// Census functions:
// strip-types.mts#stripTypes
import * as nodeModule from "node:module";
export function stripper(): unknown {
  return Object.getOwnPropertyDescriptor(nodeModule, "stripTypeScriptTypes")
    ?.value;
}
