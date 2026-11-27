// Explicit type argument `{ readonly names: number }` violates `AllInputDefs` bound directly in Lean.
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
  },
): SkipService<Record<string, never>, ResourceInputs>;

export function bad(): Promise<SkipServer> {
  return runService<{ readonly names: number }, {}>({
    inputs: { names: 42 },
    resources: {},
    createGraph: () => ({}),
  });
}
