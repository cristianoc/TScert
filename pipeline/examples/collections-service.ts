// Service: field initializers, an empty record, an index-signature
// field holding class values, and `new` with type arguments. The resource
// classes come first: a class is not hoisted.
import type {
  Context,
  EagerCollection,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  Resource,
  ResourceClass,
  Service,
} from "@fixture/collections";
import { InputDefinition } from "@fixture/collections";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
  readonly input2: EagerCollection<string, number>;
}
interface Inputs extends NamedInputDefinitions {
  readonly input1: InputDefinition<string, number>;
  readonly input2: InputDefinition<string, number>;
}

class Add implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1;
  }
}
class Sub implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input2;
  }
}
class AppService implements Service<Inputs, Collections, Collections> {
  readonly inputs: Inputs = {
    input1: new InputDefinition<string, number>(),
    input2: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<Collections, never>;
  } = { add: Add, sub: Sub };
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: Collections, _context: Context): Collections {
    return inputs;
  }
}

export function make(): AppService {
  return new AppService();
}
