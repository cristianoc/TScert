// Front-end call-site instantiation of computed-type-bearing generic functions
// (`runService`, `initService`, `asLeader`, `asFollower`) and generic interfaces
// (`SkipService`, `Resource`, `ResourceClass`) with both explicit and inferred
// type arguments, plus a generic method with computed types on an external interface.
type Json =
  | number
  | string
  | boolean
  | null
  | readonly Json[]
  | { readonly [k: string]: Json };

declare class AbstractInputDefinition {
  readonly __sk_inputDefBrand: undefined;
}
declare class InputDefinition<
  K extends Json,
  V extends Json,
> extends AbstractInputDefinition {
  readonly initial: readonly [K, readonly V[]][];
  constructor(initial?: readonly [K, readonly V[]][]);
}
declare class AbstractEagerCollection {
  readonly __sk_eagerBrand: undefined;
}
declare class AbstractLazyCollection {
  readonly __sk_lazyBrand: undefined;
}
interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection {
  getUnique(key: K): V;
}
interface Context {
  readonly id: string;
}
interface SkipServer {
  close(): Promise<void>;
}
interface ServiceInstance {
  readonly running: boolean;
  reload<
    InputDefs extends AllInputDefs<InputDefs>,
    ResourceInputs extends AllSharedCollections<ResourceInputs>,
  >(
    service: SkipService<InputDefs, ResourceInputs>,
  ): Promise<void>;
}

type InputCollections<Defs> = {
  readonly [K in keyof Defs]: Defs[K] extends InputDefinition<
    infer Key,
    infer Val
  >
    ? EagerCollection<Key, Val>
    : never;
};
type AllInputDefs<T> = { readonly [K in keyof T]: AbstractInputDefinition };
type AllSharedCollections<T> = {
  readonly [K in keyof T]: AbstractEagerCollection | AbstractLazyCollection;
};

interface Resource<Collections extends AllSharedCollections<Collections>> {
  instantiate(
    collections: Collections,
    context: Context,
  ): AbstractEagerCollection;
}
interface ResourceClass<
  Collections extends AllSharedCollections<Collections>,
  Params extends Json = Json,
> {
  new (params: Params): Resource<Collections>;
}
interface SkipService<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
> {
  readonly inputs: InputDefs;
  readonly resources: {
    readonly [name: string]: ResourceClass<ResourceInputs, Json>;
  };
  readonly createGraph: (
    inputs: InputCollections<InputDefs>,
    context: Context,
  ) => ResourceInputs;
}

declare function runService<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(service: SkipService<InputDefs, ResourceInputs>): Promise<SkipServer>;

declare function initService<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(service: SkipService<InputDefs, ResourceInputs>): Promise<ServiceInstance>;

declare function asLeader<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(
  service: SkipService<InputDefs, ResourceInputs>,
): SkipService<InputDefs, ResourceInputs>;

declare function asFollower<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(
  service: SkipService<InputDefs, ResourceInputs>,
  leader: {
    readonly leader: {
      readonly host: string;
      readonly streaming_port: number;
      readonly control_port: number;
    };
    readonly collections: readonly (keyof ResourceInputs & string)[];
    readonly lazies?: Partial<
      Record<
        keyof ResourceInputs & string,
        (context: Context) => AbstractLazyCollection
      >
    >;
  },
): SkipService<Record<string, never>, ResourceInputs>;

class Names
  implements Resource<{ readonly names: EagerCollection<string, string> }>
{
  constructor(_params: Json) {}
  instantiate(
    collections: { readonly names: EagerCollection<string, string> },
    _context: Context,
  ): AbstractEagerCollection {
    return collections.names;
  }
}

interface ExplicitDefs {
  readonly names: InputDefinition<string, string>;
}
interface ExplicitRI {
  readonly names: EagerCollection<string, string>;
}

export async function runAll(): Promise<boolean> {
  // 1. Inferred type arguments, pass-through `(ic) => ic`.
  const s1 = await runService({
    inputs: { names: new InputDefinition<string, string>([["a", ["x"]]]) },
    resources: { names: Names },
    createGraph: (ic) => ic,
  });
  // 2. Explicit type arguments.
  const explicitService: SkipService<ExplicitDefs, ExplicitRI> = {
    inputs: { names: new InputDefinition<string, string>([["b", ["y"]]]) },
    resources: { names: Names },
    createGraph: (ic) => ({ names: ic.names }),
  };
  const s2 = await runService<ExplicitDefs, ExplicitRI>(explicitService);
  // 3. asLeader & asFollower chained into runService.
  const leader = asLeader(explicitService);
  const follower = asFollower(explicitService, {
    leader: { host: "localhost", streaming_port: 8080, control_port: 8081 },
    collections: ["names"],
  });
  const s3 = await runService(leader);
  const s4 = await runService(follower);
  // 4. initService returning ServiceInstance (with generic reload method).
  const inst = await initService(explicitService);
  await s1.close();
  await s2.close();
  await s3.close();
  await s4.close();
  return inst.running;
}
