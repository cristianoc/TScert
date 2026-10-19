// Read by pipeline/test.mts on the stand-in family package: `text`, required
// in every shape, is called; `describe`, declared optional, is each shape's
// own optional member, and calling it is refused.
import type { First } from "@fixture/family";

export function text(n: First): string {
  return n.text();
}
