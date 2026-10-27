// `readdirSync` with `withFileTypes` gives a fresh array of entries; each
// `is…` test returns an unknown value and has unrestricted effects.
import { readdirSync, type Dirent } from "node:fs";

export function directories(dir: string): string[] {
  const names: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (entry.isDirectory()) names.push(entry.name);
  }
  return names;
}
// An entry named by `Dirent`, which the overlay of library types states, in
// an annotation and as a closure's parameter TypeScript types from its
// context.
export function links(dir: string): string[] {
  const entries: Dirent[] = readdirSync(dir, { withFileTypes: true });
  const found: string[] = [];
  entries.forEach((entry) => {
    if (entry.isSymbolicLink()) found.push(entry.name);
  });
  return found;
}
