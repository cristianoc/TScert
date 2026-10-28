// An indexed access into an imported union alias is every member's type at
// the key: `Shape["kind"]` is "circle" or "square", no value of "circle"
// alone.
import type { Shape } from "@fixture/lib";
export function circle(kind: Shape["kind"]): "circle" {
  return kind;
}
