// AddIndex: a constructor parameter property read by a method.
import type { Values, Mapper } from "@fixture/collections";
class AddIndex implements Mapper<string, number, string, [number, number]> {
  constructor(private index: number) {}
  mapEntry(
    key: string,
    values: Values<number>,
  ): Iterable<[string, [number, number]]> {
    return [[key, [this.index, values.getUnique()]]];
  }
}
export function use(v: Values<number>): Iterable<[string, [number, number]]> {
  return new AddIndex(0).mapEntry("k", v);
}
