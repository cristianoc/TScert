// `statSync` with `bigint: true` returns a fresh `BigIntStats`, its numbers
// bigints (run under Node), read at the type the overlay of library types
// states, and `readdirSync` without options a fresh array of names; a
// file's digest of its bytes.
import { createHash } from "node:crypto";
import { readdirSync, readFileSync, statSync, type BigIntStats } from "node:fs";

export function signature(
  path: string,
  s: BigIntStats = statSync(path, { bigint: true }),
): string {
  return `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
}
export function digest(at: string): string {
  const s = statSync(at, { bigint: true });
  if (s.isDirectory() !== true)
    return createHash("sha256").update(readFileSync(at)).digest("hex");
  const names = readdirSync(at).sort();
  return names.join("\0");
}
