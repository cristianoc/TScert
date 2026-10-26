// A spread copies a `Hash`'s own properties, and `digest` is
// `Hash.prototype`'s (run under Node: the copy's `digest` is undefined, and
// calling it throws a TypeError): the copy has no `digest`, refused.
import { createHash } from "node:crypto";

export function use(s: string): string {
  const copy = { ...createHash("sha256").update(s) };
  return copy.digest("hex");
}
