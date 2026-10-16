// `[number, number] & DepSafe` is the tuple's meet with each of DepSafe's
// alternatives: DepSafe admits numbers, but no tuple is one, so the value is
// not a number.
import type { Values } from "@fixture/collections";
export function whole(values: Values<[number, number]>): number {
  // @ts-expect-error: a tuple is not a number
  return values.getUnique();
}
