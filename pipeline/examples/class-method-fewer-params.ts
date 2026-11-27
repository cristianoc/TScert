// Concrete non-ambient class methods (and constructors) without rest
// parameters discard actuals past their declared parameters, so they meet
// signatures binding more parameters and variadic signatures.
class DeclaresOne {
  m(a: number): number {
    return a;
  }
}

interface TwoParams {
  m(a: number, b: string): number;
}

interface VariadicMethod {
  m(a: number, ...rest: string[]): number;
}

export function passInstance(): TwoParams {
  return new DeclaresOne();
}

export function passVariadic(): VariadicMethod {
  return new DeclaresOne();
}

export function callDirect(flag: boolean): number {
  const d = new DeclaresOne();
  if (flag && d.m(1) > 0) return d.m(2);
  return 0;
}

interface Inputs {
  readonly names: string;
}

interface Resource<C> {
  instantiate(collections: C, context: number): string;
}

type ResourceClass<C> = new (params: string) => Resource<C>;

class Names implements Resource<Inputs> {
  constructor(private readonly p: string) {}
  instantiate(collections: Inputs): string {
    return collections.names;
  }
}

class Add implements Resource<Inputs> {
  instantiate(collections: Inputs): string {
    return collections.names;
  }
}

declare function takeService<R>(s: {
  readonly resources: { readonly [k: string]: ResourceClass<R> };
}): void;

export const singleNames: ResourceClass<Inputs> = Names;
export const singleAdd: ResourceClass<Inputs> = Add;

export function getNames(): ResourceClass<Inputs> {
  return Names;
}

export function getAdd(): ResourceClass<Inputs> {
  return Add;
}

export function registerResources(): void {
  takeService<Inputs>({ resources: { names: Names, add: Add } });
}

// Generic class methods without their own type parameters also offer
// variadic arity across instantiations.
class Box<T> {
  constructor(private readonly v: T) {}
  get(x: T): T {
    return x;
  }
  read(): T {
    return this.v;
  }
}

interface TwoBox<T> {
  get(x: T, extra: string): T;
  read(extra: boolean): T;
}

export function passGeneric(): TwoBox<number> {
  return new Box<number>(1);
}

// Sound subclass overrides: same parameter list or fewer parameters.
class Base {
  m(a: number): number {
    return a;
  }
}

class SubSame extends Base {
  m(a: number): number {
    return a + 1;
  }
}

class SubFewer extends Base {
  m(): number {
    return 0;
  }
}

export function useSubs(): number {
  const a: TwoParams = new SubSame();
  const b: TwoParams = new SubFewer();
  return a.m(1, "x") + b.m(2, "y");
}
