// `toArray()` gives a writable array of `[number, number] & DepSafe`, which is
// strictly below the tuple: a writable array of tuples would admit writes of
// tuples that are not DepSafe, so it is refused, though TypeScript's covariant
// arrays accept it.
import type { Values } from "@fixture/collections";
export function pairs(values: Values<[number, number]>): [number, number][] {
  return values.toArray();
}
