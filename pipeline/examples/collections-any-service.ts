// A service class that is an AnyService: its createGraph takes any
// NamedEagerCollections, as the erased interface asks. The instance meets it
// member by member: the fields `inputs` and `resources` (a dictionary of
// construct signatures), the writable dictionary `externalServices` at the
// readonly optional field, and the method `createGraph`.
import type {
  AnyService,
  Context,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  ResourceClass,
  SharedCollections,
} from "@fixture/collections";
import { InputDefinition } from "@fixture/collections";

class Service {
  readonly inputs: NamedInputDefinitions = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<SharedCollections, never>;
  } = {};
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
