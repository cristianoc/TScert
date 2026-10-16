// AddIndex maps to [number, number]: a tuple type argument meets
// `V2 extends Json` as a readonly (Json | null)[], reading its elements.
import type { Mapper } from "@fixture/collections";
export function keep(
  m: Mapper<string, number, string, [number, number]>,
): Mapper<string, number, string, [number, number]> {
  return m;
}
