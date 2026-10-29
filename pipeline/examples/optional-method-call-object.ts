// An optional call of a method on any object, `e.m?.(a)`: the object
// evaluated once and saved, the member read off it once and tested,
// `undefined` where absent, else called with the saved object as its
// receiver. The census function it stands for:
// declaration-graph.mts#collectDeclarations
// (`valueScope(client, …).equation?.(reference) ?? null`). Each run under
// Node: the object's call runs once, and the method sees it as `this`.
interface Scope {
  readonly base: number;
  equation?(x: number): number;
}

function current(scope: Scope, log: string[]): Scope {
  log.push("object");
  return scope;
}

// The object a call.
export function apply(scope: Scope, x: number, log: string[]): number | null {
  return current(scope, log).equation?.(x) ?? null;
}

// The object a `let` the function assigns.
export function assigned(first: Scope, second: Scope, x: number): number | undefined {
  let scope = first;
  scope = second;
  return scope.equation?.(x);
}

interface Holder {
  readonly scope?: Scope;
}

// A link of an optional chain: the earlier `?.` skips the call.
export function linked(holder: Holder | undefined, x: number): number | undefined {
  return holder?.scope?.equation?.(x);
}

interface Result {
  readonly n: number;
}
interface Maker {
  readonly make?: (this: Maker, k: number) => Result;
}

// A link after the call, skipped with it; the method's `this` parameter met
// by the saved object.
export function after(maker: Maker, k: number): number | undefined {
  return maker.make?.(k).n;
}
