// Exact overload matches across constructors, callables and methods: when a
// source signature list already holds the target overload, premise discovery
// skips comparing that target against the source's other overloads.
type Entry =
  | { readonly kind: "leaf"; readonly value: number }
  | { readonly kind: "pair"; readonly left: Entry; readonly right: Entry };

type Ledger = { readonly entries: Map<string, Entry> };

export function newLedger(): Ledger {
  return { entries: new Map() };
}

interface OverloadedFn {
  (x: number): number;
  (tree: Entry, pairs: readonly (readonly [string, Entry])[]): Entry;
}

type OverloadedMethods = {
  pick(x: number): number;
} & {
  pick(tree: Entry, pairs: readonly (readonly [string, Entry])[]): Entry;
};

type OverloadedMethodField = {
  readonly pick: OverloadedFn;
};

export function narrowCallable(f: OverloadedFn): (x: number) => number {
  return f;
}

export function narrowMethod(h: OverloadedMethods): {
  pick(x: number): number;
} {
  return h;
}

export function narrowMethodField(h: OverloadedMethodField): {
  pick(x: number): number;
} {
  return h;
}
