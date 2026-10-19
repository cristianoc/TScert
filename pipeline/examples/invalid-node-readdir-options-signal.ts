// Options whose type states no `signal` may hold it as a getter, which Node
// reads between its two reads of `encoding`: one switching `encoding` to
// "buffer" names the entries by Buffers (run under Node). The reviewed
// options state `signal` absent, so this record is refused.
import { readdirSync } from "node:fs";

export function names(
  dir: string,
  options: { withFileTypes: true; encoding?: "utf8"; recursive?: false },
): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, options)) found.push(entry.name);
  return found;
}
