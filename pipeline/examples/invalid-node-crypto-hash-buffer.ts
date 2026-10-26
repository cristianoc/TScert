// `digest()` without an encoding returns a `Buffer` (run under Node): outside
// the reviewed `digest`, refused.
import { createHash } from "node:crypto";

export function use(s: string): unknown {
  return createHash("sha256").update(s).digest();
}
