// `node:fs`'s `mkdtempSync` at a string prefix returns the new directory's
// path, and `rmSync` at a string path and `{ recursive: true, force: true }`
// removes it: both through the reviewed overlay, so `Buffer` is not read.
import { mkdtempSync, rmSync } from "node:fs";

export function scratch(prefix: string): string {
  const made = mkdtempSync(prefix);
  rmSync(made, { recursive: true, force: true });
  return made;
}
