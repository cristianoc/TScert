// `createHash("sha256")` through its reviewed entry: `update` at strings,
// chained and as statements, and `digest("hex")`, a string. A second
// `digest` throws (run under Node: `ERR_CRYPTO_HASH_FINALIZED`), an outcome.
import { createHash } from "node:crypto";

export function digestOf(version: string, files: readonly string[]): string {
  const hash = createHash("sha256");
  hash.update(`${version}\0`);
  for (const file of files) {
    hash.update(`${file}\0`).update("\0");
  }
  return hash.digest("hex");
}

export function twice(s: string): string {
  const hash = createHash("sha256").update(s);
  const first = hash.digest("hex");
  return first + hash.digest("hex");
}
