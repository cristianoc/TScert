// A module’s own enumerable exports, copied through the module-loading host
// boundary after its reads are observed. The caller holds a map.
// Census functions: family-activation.mts#checkedGuards, #activateGuards,
// #loadedGuards, #activeGuards, #guardOfExport.
import { loadModule } from "../../tools/files.mts";

export function exportsOf(
  root: string,
  path: string,
): ReadonlyMap<string, unknown> | null {
  return loadModule(root, path);
}
