// An entry's prototype reached through its constructor.
import { readdirSync } from "node:fs";

export function replace(dir: string): void {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    entry.constructor.prototype.isDirectory = () => true;
  }
}
