// A resource class whose constructor needs more than Json, held where a
// resource is constructed with any Json: `Labeled` calls its parameter's
// `toString`. TypeScript accepts it, since every Json value has
// `Object.prototype.toString`; but a Json object may own the key `toString`
// at any Json (`{"toString": 1}`), and `label()` then calls a number.
import type {
  EagerCollection,
  Json,
  NamedEagerCollections,
  Resource,
  ResourceClass,
} from "@fixture/collections";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}

class Labeled implements Resource<Collections> {
  constructor(readonly params: { readonly toString: () => string }) {}
  label(): string {
    return this.params.toString();
  }
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1;
  }
}

export const resources: {
  readonly [name: string]: ResourceClass<Collections, Json>;
} = { labeled: Labeled };
