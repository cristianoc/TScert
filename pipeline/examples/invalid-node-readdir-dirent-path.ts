// The declaration gives a `Dirent` a `path`, which Node 25 no longer sets
// (run under Node: `undefined`): refused as a string.
import { readdirSync } from "node:fs";

export function paths(dir: string): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true }))
    found.push(entry.path);
  return found;
}
