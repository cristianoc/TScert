// Add: an interface extending a library interface, and a class value
// passed to a generic method.
import type {
  Values,
  Mapper,
  EagerCollection,
  Resource,
  NamedEagerCollections,
} from "@fixture/collections";
class Plus implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique()]];
  }
}
interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
  readonly input2: EagerCollection<string, number>;
}
class Add implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1.merge(cs.input2).map(Plus);
  }
}
export function use(cs: Collections): EagerCollection<string, number> {
  return new Add().instantiate(cs);
}
