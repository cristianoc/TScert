// A record keyed by another symbol does not carry this brand.
import { mark, unwrap } from "@fixture/lib";
export function forged(n: number): number {
  return unwrap(mark(n));
}
