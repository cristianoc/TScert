// `encoding: "buffer"` beside `withFileTypes` names each entry by a Buffer
// (run under Node), though the declaration says `string`: the reviewed
// options admit `"utf8"` alone, so the call is refused.
import { readdirSync } from "node:fs";

export function names(dir: string): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, {
    withFileTypes: true,
    encoding: "buffer",
  }))
    found.push(entry.name);
  return found;
}
