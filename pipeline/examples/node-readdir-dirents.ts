// `readdirSync` with `withFileTypes` gives a fresh array of entries, each
// answering whether it is a directory without running code.
import { readdirSync } from "node:fs";

export function directories(dir: string): string[] {
  const names: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (entry.isDirectory()) names.push(entry.name);
  }
  return names;
}
