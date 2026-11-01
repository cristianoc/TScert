// A replaced posix.normalize can shrink the shared map receiver, leaving a hole that Set iterates as undefined.
import { join } from "node:path";
export function paths(root: string, inventory: string[]): Set<string> {
  return new Set(inventory.map((file) => join(root, ...file.split("/"))));
}
