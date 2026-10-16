// A typed library of reactive collections: recursive JSON values, values
// marked by a symbol key, generic collection interfaces whose methods take
// classes, and a service interface. The examples import it at its declared
// types; its bodies are not verified.

export const managed: unique symbol = Symbol.for("fixture.managed");

/** A value the library tracks, or a deep-frozen one: it owns `managed`. */
export type Managed = { [managed]: true };

/** A value safe to depend on: a primitive, or a managed value. */
export type DepSafe =
  | null
  | boolean
  | number
  | bigint
  | string
  | symbol
  | Managed;

export type Json =
  | boolean
  | number
  | string
  | readonly (Json | null)[]
  | JsonObject;
export type JsonObject = { readonly [key: string]: Json | null };

export function deepFreeze<T>(value: T): T & DepSafe {
  if (typeof value === "object" && value !== null) {
    for (const v of Object.values(value)) deepFreeze(v);
    Object.defineProperty(value, managed, {
      enumerable: false,
      writable: false,
      value: true,
    });
    return Object.freeze(value) as T & DepSafe;
  }
  if (typeof value === "function" || value === undefined)
    throw new Error("not freezable");
  return value as T & DepSafe;
}

export abstract class AbstractEagerCollection {
  readonly __collectionBrand: undefined;
}
export abstract class AbstractLazyCollection {
  readonly __lazyCollectionBrand: undefined;
}

export interface Mapper<
  K1 extends Json,
  V1 extends Json,
  K2 extends Json,
  V2 extends Json,
> {
  mapEntry(key: K1, values: Values<V1>, context: Context): Iterable<[K2, V2]>;
}

export interface Reducer<V extends Json, A extends Json> {
  initial: A | null;
  add(accum: A | null, value: V & DepSafe): A;
  remove(accum: A, value: V & DepSafe): A | null;
}

export interface Values<T> extends Iterable<T & DepSafe> {
  getUnique(_default?: { ifMany?: T }): T & DepSafe;
  toArray(): (T & DepSafe)[];
}

export interface LazyCollection<K extends Json, V extends Json>
  extends AbstractLazyCollection,
    Managed {
  getArray(key: K): (V & DepSafe)[];
  getUnique(key: K, _default?: { ifNone?: V; ifMany?: V }): V & DepSafe;
}

export interface EagerCollection<K extends Json, V extends Json>
  extends AbstractEagerCollection,
    Managed {
  getArray(key: K): (V & DepSafe)[];
  getUnique(key: K, _default?: { ifNone?: V; ifMany?: V }): V & DepSafe;
  map<K2 extends Json, V2 extends Json, Params extends readonly DepSafe[]>(
    mapper: new (...params: Params) => Mapper<K, V, K2, V2>,
    ...params: Params
  ): EagerCollection<K2, V2>;
  reduce<Accum extends Json, Params extends readonly DepSafe[]>(
    reducer: new (...params: Params) => Reducer<V, Accum>,
    ...params: Params
  ): EagerCollection<K, Accum>;
  slice(start: K & DepSafe, end: K & DepSafe): EagerCollection<K, V>;
  take(limit: number): EagerCollection<K, V>;
  merge(...others: EagerCollection<K, V>[]): EagerCollection<K, V>;
  size(): number;
}

export interface LazyCompute<K extends Json, V extends Json> {
  compute(self: LazyCollection<K, V>, key: K, context: Context): Iterable<V>;
}

export interface Context {
  createLazyCollection<
    K extends Json,
    V extends Json,
    Params extends readonly DepSafe[],
  >(
    compute: new (...params: Params) => LazyCompute<K, V>,
    ...params: Params
  ): LazyCollection<K, V>;
  useExternalResource<K extends Json, V extends Json>(resource: {
    service: string;
    identifier: string;
    params?: Json;
  }): EagerCollection<K, V>;
  jsonExtract(value: JsonObject, pattern: string): Json[];
}

export type Entry<K extends Json, V extends Json> = [K, V[]];

export interface ExternalService {
  subscribe(
    instance: string,
    resource: string,
    params: Json,
    callbacks: {
      update: (updates: Entry<Json, Json>[], isInit: boolean) => Promise<void>;
      error: (error: unknown) => void;
    },
  ): Promise<void>;
  unsubscribe(instance: string): void;
  shutdown(): Promise<void>;
}

export type NamedEagerCollections = {
  readonly [name: string]: AbstractEagerCollection;
};
export type SharedCollections = {
  readonly [name: string]: AbstractEagerCollection | AbstractLazyCollection;
};

export interface Resource<Collections extends SharedCollections> {
  instantiate(
    collections: Collections,
    context: Context,
  ): AbstractEagerCollection;
}
export type ResourceClass<
  Collections extends SharedCollections,
  Params extends Json,
> = new (params: Params) => Resource<Collections>;

export abstract class AbstractInputDefinition {
  readonly __inputDefBrand: undefined;
}
export class InputDefinition<
  K extends Json,
  V extends Json,
> extends AbstractInputDefinition {
  readonly initial: Entry<K, V>[];
  constructor(initial: Entry<K, V>[] = []) {
    super();
    this.initial = initial;
  }
}
export type NamedInputDefinitions = {
  readonly [name: string]: AbstractInputDefinition;
};

export interface Service<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends SharedCollections,
> {
  readonly inputs: InputDefs;
  readonly externalServices?: { readonly [name: string]: ExternalService };
  readonly resources: {
    readonly [name: string]: ResourceClass<ResourceInputs, never>;
  };
  createGraph(inputCollections: Inputs, context: Context): ResourceInputs;
}
export type AnyService = Service<
  NamedInputDefinitions,
  NamedEagerCollections,
  SharedCollections
>;

export type Server = { close: () => Promise<void> };

export async function runService(
  service: AnyService,
  options: {
    streaming_port: number;
    control_port: number;
    platform?: "wasm" | "native";
    no_cors?: boolean;
  } = {
    streaming_port: 8080,
    control_port: 8081,
    platform: "wasm",
    no_cors: false,
  },
): Promise<Server> {
  void service;
  void options;
  return { close: async () => {} };
}
