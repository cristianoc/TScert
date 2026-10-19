// With `recursive: true` Node walks the subdirectories, calling each
// entry's `isDirectory` through its prototype and `path.join` to choose what
// to read next (run under Node: a replaced `isDirectory` runs during the
// call): the reviewed options admit `recursive` false or absent, refused.
import { readdirSync } from "node:fs";

export function walk(dir: string): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, {
    withFileTypes: true,
    recursive: true,
  }))
    found.push(entry.name);
  return found;
}
