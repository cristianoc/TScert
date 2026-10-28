// A tuple projected through an imported alias retains both number elements.
import type { Shape } from "@fixture/lib";
export function x(at: Shape["at"]): [string, string] {
  return at;
}
