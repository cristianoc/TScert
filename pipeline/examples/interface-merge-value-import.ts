// An interface its module declares twice, imported: TypeScript merges the two
// declarations, and the declaration reader reads them as one.
import type { Merge } from "@fixture/lib";
export function readMerged(value: Merge): boolean {
  return value.flag;
}
