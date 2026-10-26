// `digest("base64")`: the reviewed `digest` takes "hex" alone, refused.
import { createHash } from "node:crypto";

export function use(s: string): string {
  return createHash("sha256").update(s).digest("base64");
}
