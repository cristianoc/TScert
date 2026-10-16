// A mapper whose mapEntry takes fewer parameters, one of them narrower than
// Mapper.mapEntry's: TypeScript's bivariant method parameters admit it, but
// map calls it with any string key, so the class is refused.
import type {
  Values,
  Mapper,
  EagerCollection,
  Resource,
  NamedEagerCollections,
} from "@fixture/collections";
class Plus implements Mapper<string, number, string, number> {
  mapEntry(key: "k", values: Values<number>): Iterable<[string, number]> {
    return [[key, values.getUnique()]];
  }
}
interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}
class Add implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1.map(Plus);
  }
}
export function use(cs: Collections): EagerCollection<string, number> {
  return new Add().instantiate(cs);
}
