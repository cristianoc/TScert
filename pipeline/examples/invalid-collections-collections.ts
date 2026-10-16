// TypeScript gives a type literal an implicit index signature, so it accepts
// this record as Collections. It states nothing of the record's other keys,
// which NamedEagerCollections constrains: it is not a Collections.
import type {
  EagerCollection,
  NamedEagerCollections,
} from "@fixture/collections";
interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}
export function promote(r: {
  readonly input1: EagerCollection<string, number>;
}): Collections {
  return r;
}
