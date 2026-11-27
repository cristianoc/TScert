export type Json =
  | number
  | string
  | boolean
  | null
  | readonly Json[]
  | { readonly [k: string]: Json };

export abstract class AbstractInputDefinition {
  readonly __sk_inputDefBrand: undefined;
}
export declare class InputDefinition<
  K extends Json,
  V extends Json,
> extends AbstractInputDefinition {
  readonly initial: readonly [K, readonly V[]][];
  constructor(initial?: readonly [K, readonly V[]][]);
}
export abstract class AbstractEagerCollection {
  readonly __sk_eagerBrand: undefined;
}
export abstract class AbstractLazyCollection {
  readonly __sk_lazyBrand: undefined;
}
export interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection {
  getUnique(key: K): V;
}
export interface Context {
  readonly id: string;
}
export interface SkipServer {
  close(): Promise<void>;
}
export interface ServiceInstance {
  readonly running: boolean;
  reload<
    InputDefs extends AllInputDefs<InputDefs>,
    ResourceInputs extends AllSharedCollections<ResourceInputs>,
  >(
    service: SkipService<InputDefs, ResourceInputs>,
  ): Promise<void>;
}

export type InputCollections<Defs> = {
  readonly [K in keyof Defs]: Defs[K] extends InputDefinition<
    infer Key,
    infer Val
  >
    ? EagerCollection<Key, Val>
    : never;
};
export type AllInputDefs<T> = {
  readonly [K in keyof T]: AbstractInputDefinition;
};
export type AllSharedCollections<T> = {
  readonly [K in keyof T]: AbstractEagerCollection | AbstractLazyCollection;
};

export interface Resource<
  Collections extends AllSharedCollections<Collections>,
> {
  instantiate(
    collections: Collections,
    context: Context,
  ): AbstractEagerCollection;
}
export interface ResourceClass<
  Collections extends AllSharedCollections<Collections>,
  Params extends Json = Json,
> {
  new (params: Params): Resource<Collections>;
}
export interface SkipService<
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

export declare function runService<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(service: SkipService<InputDefs, ResourceInputs>): Promise<SkipServer>;

export declare function initService<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(service: SkipService<InputDefs, ResourceInputs>): Promise<ServiceInstance>;

export declare function asLeader<
  InputDefs extends AllInputDefs<InputDefs>,
  ResourceInputs extends AllSharedCollections<ResourceInputs>,
>(
  service: SkipService<InputDefs, ResourceInputs>,
): SkipService<InputDefs, ResourceInputs>;

export declare function asFollower<
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
