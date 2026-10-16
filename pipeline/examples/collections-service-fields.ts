// Service, over library types that extend no interface: field
// initializers run by `new`; `new` with explicit type arguments and an
// omitted optional argument; a readonly dictionary of classes constructible
// at `never`; and an empty mutable dictionary.
import type {
  AbstractEagerCollection,
  Context,
  ExternalService,
  Resource,
  ResourceClass,
} from "@fixture/collections";
import { InputDefinition } from "@fixture/collections";

type Collections = { readonly [name: string]: AbstractEagerCollection };
type Inputs = {
  readonly input1: InputDefinition<string, number>;
  readonly input2: InputDefinition<string, number>;
};

class Add implements Resource<Collections> {
  constructor(private readonly output: AbstractEagerCollection) {}
  instantiate(_cs: Collections, _context: Context): AbstractEagerCollection {
    return this.output;
  }
}

class Service {
  readonly inputs: Inputs = {
    input1: new InputDefinition<string, number>(),
    input2: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<Collections, never>;
  } = { add: Add };
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: Collections, _context: Context): Collections {
    return inputs;
  }
}

export function make(): Service {
  return new Service();
}
