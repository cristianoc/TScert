// A library whose values the examples import. Nothing here is checked by the
// verifier: each import is assumed at the type its declaration states.
export function double(x: number): number {
  return x + x;
}
export const limit: number = 10;
export class Counter {
  count: number;
  constructor(start: number) {
    this.count = start;
  }
  bump(): number {
    this.count = this.count + 1;
    return this.count;
  }
}
export function generic<T>(x: T): T {
  return x;
}
export class Holder<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}
export class Keeper<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  get(): T {
    return this.value;
  }
}
export class Tagged {
  readonly tag: number = 1;
}
export class Named extends Tagged {
  readonly name: string = "named";
}
// Two brands, keyed by distinct unique symbols: a value carries one brand's
// key and not the other's.
export const brand: unique symbol = Symbol("brand");
export const other: unique symbol = Symbol("other");
// Two constants made by `Symbol.for` of one string: the registry gives both
// the same symbol, though TypeScript types each a distinct unique symbol.
export const sharedLeft: unique symbol = Symbol.for("fixture.shared");
export const sharedRight: unique symbol = Symbol.for("fixture.shared");
export type Branded = { [brand]: true; n: number };
export type Marked = { [other]: true; n: number };
export function wrap(n: number): Branded {
  return { [brand]: true, n };
}
export function mark(n: number): Marked {
  return { [other]: true, n };
}
export function unwrap(b: Branded): number {
  return b.n;
}
// Generic methods: `pick` returns one of its arguments, at the type a call
// instantiates; a `Cell`'s `with` makes a cell of another type.
export interface Chooser {
  pick<T>(first: T, second: T): T;
}
export const chooser: Chooser = { pick: (first, second) => first };
export interface Cell<T> {
  readonly value: T;
  with<U>(value: U): Cell<U>;
}
// A generic method with a bounded binder: `either` returns one of two
// Booleans, at the Boolean type a call instantiates.
export interface Flags {
  either<T extends boolean>(first: T, second: T): T;
}
export const flags: Flags = { either: (first, second) => first };
// A generic method with a pack parameter, as `EagerCollection.map`: its rest
// is typed by a binder that a construct type's rest shares, so a call passes
// a class and the actuals its constructor takes.
export class Box {
  v: number;
  constructor(v: number) {
    this.v = v;
  }
}
export interface Maker {
  make<Params extends number[]>(
    cls: new (...params: Params) => Box,
    ...params: Params
  ): Box;
}
export const maker: Maker = { make: (cls, ...params) => new cls(...params) };

// Constructor operands use the same nested object contracts as function operands.
export class ObjectBox {
  v: { readonly value: number };
  constructor(v: { readonly value: number }) {
    this.v = v;
  }
}

// A generic method whose pack parameter is a tuple of objects: the
// constructor's contract and the trailing actuals share one argument list.
export interface ObjectMaker {
  make<Params extends { readonly value: number }[]>(
    cls: new (...params: Params) => ObjectBox,
    ...params: Params
  ): ObjectBox;
}
export const objectMaker: ObjectMaker = {
  make: (cls, ...params) => new cls(...params),
};

// A marked array, as a library may mark the arrays it manages: an own key
// under a unique symbol, which the array's prototype does not provide.
export const managed: unique symbol = Symbol("managed");
export type Managed = { readonly [managed]: true };
export type Unmarked = { readonly [managed]: false };
export function managedPair(): [number, number] & Managed {
  return Object.defineProperty([1, 2], managed, { value: true }) as [
    number,
    number,
  ] &
    Managed;
}
export function isManaged(m: Managed): true {
  return m[managed];
}

// A function with overloads: callers see the two overloads, not the
// implementation's signature.
export function either(x: number): number;
export function either(x: string): string;
export function either(x: number | string): number | string {
  return x;
}

/** An interface declared twice in this module, which TypeScript merges; the
 * case interface-merge-value-import-refused imports it. */
export interface Merge {
  readonly flag: boolean;
}
export interface Merge {
  readonly label: string;
}

// A bounded alias an import type applies (`invalid-written-import-type-value-import`).
export type Bounded<T extends string> = T;

// A class whose heritage calls a generic function
// (`invalid-written-heritage-call-value-import`).
function made<T>(): { new (): { n: number } } {
  return class {
    n = 1;
  };
}
export class Made extends made<Bounded<any>>() {}
