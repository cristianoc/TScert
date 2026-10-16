// A Mapper: a method whose parameter is a generic interface application.
import type { Values, Mapper } from "@fixture/collections";
class Plus implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique()]];
  }
}
export function use(v: Values<number>): Iterable<[string, number]> {
  return new Plus().mapEntry("k", v);
}
