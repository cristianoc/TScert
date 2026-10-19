// Read by pipeline/test.mts on the stand-in family package: `describe` is
// declared optional, so a shape states it optional and the call is refused.
import type { First } from "@fixture/family";

export function describe(n: First): string {
  return n.describe();
}
