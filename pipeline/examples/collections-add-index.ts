// Sub: `.map(AddIndex, 0)` instantiates EagerCollection.map at
// `V2 := [number, number]`, a tuple, which is not DepSafe. Its result
// `EagerCollection<K2, V2>` holds `V2 & DepSafe`, a meet row, whose instance is
// the tuple's meet with DepSafe: the row the ground application has.
import type { EagerCollection, Mapper, Values } from "@fixture/collections";
class AddIndex implements Mapper<string, number, string, [number, number]> {
  constructor(private index: number) {}
  mapEntry(
    key: string,
    values: Values<number>,
  ): Iterable<[string, [number, number]]> {
    return [[key, [this.index, values.getUnique()]]];
  }
}
class Sub {
  instantiate(
    c: EagerCollection<string, number>,
  ): EagerCollection<string, [number, number]> {
    return c.map(AddIndex, 0);
  }
}
export function use(
  c: EagerCollection<string, number>,
): EagerCollection<string, [number, number]> {
  return new Sub().instantiate(c);
}
