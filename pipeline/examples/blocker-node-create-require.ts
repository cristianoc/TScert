// The imported createRequire signature needs the type reader to read its
// result type, NodeJS.Require.
// Census functions:
// files.mts#loadModule.
import { createRequire } from "node:module";
export function use(path: string): void {
  createRequire(path);
}
