// Listing a lazy collection in `collections` violates
// `Eager <= readonly EagerKeys<ResourceInputs>[]`, rejected by Lean.
declare const eagerBrand: unique symbol;
declare const lazyBrand: unique symbol;
declare const missingBrand: unique symbol;

declare abstract class AbstractEager {
  readonly [eagerBrand]: never;
}

declare abstract class AbstractLazy {
  readonly [lazyBrand]: never;
}

interface EagerCol<V> extends AbstractEager {
  get(): V;
}

interface LazyCol<V> extends AbstractLazy {
  compute(): V;
}

interface Ctx {
  readonly id: string;
}

type AllShared<T> = {
  readonly [K in keyof T]: AbstractEager | AbstractLazy;
};

type EagerKeys<T> = {
  [K in keyof T & string]: [T[K]] extends [never]
    ? never
    : T[K] extends AbstractEager
      ? K
      : never;
}[keyof T & string];

type LazyKeys<T> = {
  [K in keyof T & string]: [T[K]] extends [never]
    ? never
    : T[K] extends AbstractLazy
      ? K
      : never;
}[keyof T & string];

type FollowerLazies<ResourceInputs> = [LazyKeys<ResourceInputs>] extends [never]
  ? { readonly lazies?: { readonly [K in never]: never } }
  : {
      readonly lazies: {
        readonly [K in LazyKeys<ResourceInputs>]: (
          ctx: Ctx,
        ) => ResourceInputs[K];
      };
    };

type FollowerCoverage<ResourceInputs, Eager extends readonly string[]> = [
  Exclude<EagerKeys<ResourceInputs>, Eager[number]>,
] extends [never]
  ? unknown
  : {
      readonly missingEagerCollections: readonly [
        typeof missingBrand,
        Exclude<EagerKeys<ResourceInputs>, Eager[number]>,
      ];
    };

interface Service<ResourceInputs extends AllShared<ResourceInputs>> {
  readonly resources: ResourceInputs;
}

declare function asFollower<
  ResourceInputs extends AllShared<ResourceInputs>,
  const Eager extends readonly EagerKeys<ResourceInputs>[],
>(
  service: Service<ResourceInputs>,
  config: {
    readonly collections: Eager;
  } & FollowerLazies<ResourceInputs> &
    FollowerCoverage<ResourceInputs, Eager>,
): Service<ResourceInputs>;

type Mixed = {
  readonly names: EagerCol<string>;
  readonly echo: LazyCol<number>;
};

export function rejectLazyInEager(
  svc: Service<Mixed>,
  makeEcho: (ctx: Ctx) => LazyCol<number>,
): Service<Mixed> {
  return asFollower(svc, {
    collections: ["names", "echo"],
    lazies: { echo: makeEcho },
  });
}
