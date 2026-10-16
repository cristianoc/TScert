// An interface its module declares twice, imported: TypeScript merges the two
// declarations, and the declaration reader resolves an import to one
// declaration, so it refuses the name.
import type { Merge } from "@fixture/lib";
export function readMerged(value: Merge): boolean {
  return value.flag;
}
