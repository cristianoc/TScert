// CreateGraph is not AnyService's: it takes the named
// collections `Collections`, and the erased interface may pass any
// NamedEagerCollections, one without `input1`. TypeScript accepts the
// service through its bivariant method parameters.
import type {
  AnyService,
  Context,
  EagerCollection,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  ResourceClass,
  SharedCollections,
} from "@fixture/collections";
import { InputDefinition } from "@fixture/collections";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}

class Service {
  readonly inputs: NamedInputDefinitions = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<SharedCollections, never>;
  } = {};
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: Collections, _context: Context): SharedCollections {
    return inputs;
  }
}

export function make(): AnyService {
  return new Service();
}
