// A method parameter at Values<number> admits no Values<string>: the rows the
// claim and the annotation name are compared by meaning, not merely accepted.
import type { Values, Mapper } from "@fixture/collections";
class Plus implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique()]];
  }
}
export function use(v: Values<string>): Iterable<[string, number]> {
  return new Plus().mapEntry("k", v);
}
