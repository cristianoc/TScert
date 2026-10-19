// An entry's prototype reached through the entry.
import { readdirSync } from "node:fs";

export function replace(dir: string): void {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const proto: { isDirectory: () => unknown } = Object.getPrototypeOf(entry);
    proto.isDirectory = () => true;
  }
}
