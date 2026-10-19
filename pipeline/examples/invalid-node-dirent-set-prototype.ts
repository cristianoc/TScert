// An entry given another prototype.
import { readdirSync } from "node:fs";

export function swap(dir: string): void {
  for (const entry of readdirSync(dir, { withFileTypes: true }))
    Object.setPrototypeOf(entry, null);
}
