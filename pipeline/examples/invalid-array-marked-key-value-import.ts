// A marked tuple's marker is `true`: it is not a record whose marker is
// `false`.
import type { Managed, Unmarked } from "@fixture/lib";
function unmarked(m: Unmarked): number {
  return 0;
}
export function wrong(xs: [number, number] & Managed): number {
  return unmarked(xs);
}
