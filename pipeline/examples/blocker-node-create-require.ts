// createRequire, imported from node:module, needs a reviewed entry of the
// overlay of library modules; the type reader then reads its declared result
// type, NodeJS.Require.
// Census functions:
// files.mts#loadModule.
import { createRequire } from "node:module";
export function use(path: string): void {
  createRequire(path);
}
