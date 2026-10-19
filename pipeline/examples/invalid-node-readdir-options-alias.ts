// Options typed by `withFileTypes` alone may hold `encoding: "buffer"`
// (run under Node: a Buffer name): the reviewed options state `encoding`, so
// a record that does not is refused.
import { readdirSync } from "node:fs";

export function names(dir: string, options: { withFileTypes: true }): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, options)) found.push(entry.name);
  return found;
}
