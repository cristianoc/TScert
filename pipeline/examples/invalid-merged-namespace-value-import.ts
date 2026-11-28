// An interface merged with a `namespace` remains outside the fragment and is
// still refused as a multi-declaration import.
import type { BadNamespaceMerge } from "@fixture/merged-interface-value";

export function readX(v: BadNamespaceMerge): number {
  return v.x;
}
