// Resources are not AnyService's: `Add` reads the named
// collection `input1`, and the erased interface's resources are instantiated
// at any SharedCollections, one without it. TypeScript accepts the service
// through the bivariant parameter of `Resource.instantiate`.
import type {
  AnyService,
  Context,
  EagerCollection,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  Resource,
  ResourceClass,
  SharedCollections,
} from "@fixture/collections";
import { InputDefinition } from "@fixture/collections";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}

class Add implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1;
  }
}
class Service {
  readonly inputs: NamedInputDefinitions = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<Collections, never>;
  } = { add: Add };
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(
    inputs: NamedEagerCollections,
    _context: Context,
  ): SharedCollections {
    return inputs;
  }
}

export function make(): AnyService {
  return new Service();
}
