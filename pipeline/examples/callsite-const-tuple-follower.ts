// Call-site instantiation of `const Eager` tuple parameters with mapped-index
// conditionals (`EagerKeys`, `LazyKeys`), `[X] extends [never]`, `Exclude`,
// `Tuple[number]`, `{ readonly [K in never]: never }`, and `typeof uniqueSymbol`.
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

type EagerOnly = {
  readonly names: EagerCol<string>;
};

type Mixed = {
  readonly names: EagerCol<string>;
  readonly echo: LazyCol<number>;
};

export function followAll(
  eagerSvc: Service<EagerOnly>,
  mixedSvc: Service<Mixed>,
  emptySvc: Service<Record<string, never>>,
  makeEcho: (ctx: Ctx) => LazyCol<number>,
): Service<Record<string, never>> {
  const _f1 = asFollower(eagerSvc, { collections: ["names"] });
  const _f2 = asFollower(mixedSvc, {
    collections: ["names"],
    lazies: { echo: makeEcho },
  });
  void _f1;
  void _f2;
  return asFollower(emptySvc, { collections: [] });
}
