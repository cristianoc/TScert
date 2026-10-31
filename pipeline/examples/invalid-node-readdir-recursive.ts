// With recursive: true Node collects entries from subdirectories (run
// under Node: the result includes a nested file). The reviewed options
// admit recursive false or absent, so the call is refused.
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
