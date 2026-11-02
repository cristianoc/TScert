/** The contracts of the built-in prototypes a program reads members through:
 * `ArrayProto`, the contract of `Array.prototype`, and `StringProto`,
 * `NumberProto`, `BigIntProto` and `BooleanProto`, those of the prototypes a
 * primitive's members are read from (`"a".toUpperCase()`, `n.toString(16)`).
 * Each is TypeScript's own declarations, as the project's standard library
 * states them (`ReadonlyArray<T>` and `Array<T>`; `String`, `Number`, `BigInt`,
 * `Boolean`), through a reviewed overlay. Nothing is vendored. The overlay
 * holds only what those declarations leave out and soundness needs
 * (DESIGN.md, "Trust surface"; SOURCE-CONTRACTS.md, "Prototype contracts"):
 *
 * - which members exist: any member not listed is refused, not trusted;
 * - each member's receiver: `readonly T[]` for one declared on
 *   `ReadonlyArray`, `T[]` for a mutator declared only on `Array`, the
 *   primitive itself for a primitive's member;
 * - parameters dropped (`thisArg?: any`, `locales`), which calls must then
 *   omit;
 * - which overload is kept, and any restriction or result correction needed
 *   when the native does not meet TypeScript's declared contract.
 *
 * A member that throws on some argument its declaration admits
 * (`toString(radix)` outside 2 to 36, a `RangeError`) is read as declared: a
 * throw is an outcome, never a wrong value (SOURCE-MODEL.md, "Throws").
 *
 * Each entry records the declaration text it was reviewed against. A member
 * is read only from a declaration with exactly that text, so a changed
 * library is refused here and reviewed again, never trusted silently. */
import { SymbolFlags, type Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";
import { oneTerm, signatures, typeTerm, type TermScope } from "./type-term.mts";
import type { DeclarationIdentity, ElementKind, PropertyKey, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { closedFootprints, emptyEffect, footprintEffect, ordinaryEffect, promiseEffect } from "./type-graph.mts";
import type { CallEffect, ArrayPresence, ClosedFootprint } from "./type-graph.mts";

export type OverlayEntry = {
  /** The member's key on the prototype, as declared: a name, or a computed
   * key such as `[Symbol.iterator]`. */
  name: string;
  /** Where it is declared: `ReadonlyArray` for a member that only reads the
   * array, `Array` for a mutator; the primitive's own interface, or `Object`
   * for a member TypeScript reads there that the primitive's prototype owns
   * (`Boolean.prototype.toString`). */
  from: string;
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** Parameters dropped by name: calls must omit them. */
  drop?: string[];
  /** The member's own binders a statement leaves out, each of which types
   * only what it drops (`flatMap`'s `This`, the type of `thisArg`). */
  unbound?: string[];
  /** The member's own binders, as its reviewed replacement signatures state
   * them, in place of the declaration's (`flat`'s `U`, the element type of
   * the receiver's arrays, for its `A` and `D`). */
  binders?: string[];
  /** The declared `this` result is the receiver. */
  resultIsReceiver?: boolean;
  /** The result stated as this standard library interface at the declared
   * result's one argument, which the declared result implies: a weaker
   * contract than the declaration's (`ArrayIterator<T>` read as `Iterator<T>`
   * or, keeping its `[Symbol.iterator]`, as `IterableIterator<T>`), or as
   * the native collection iterator (`NativeIterator`, a `Set`'s or a
   * `Map`'s `SetIterator<T>` or `MapIterator<T>`). */
  resultAs?: "Iterator" | "IterableIterator" | "NativeIterator";
  /** A reviewed restriction on a quantified parameter. Required when native
   * coercion could otherwise call an arbitrary client method. */
  bounds?: Map<string, TypeTerm>;
  /** A reviewed result contract replacing TypeScript's result. In particular,
   * map may produce holes and cannot promise a dense array. */
  result?: TypeTerm;
  /** A reviewed replacement signature: restrict implicit client hooks (e.g.
   * split on strings only), or correct explicit callback arguments (find
   * visits missing positions with undefined). The receiver is the prototype's. */
  stated?: StatedSignature[];
  /** The effect the member's signatures state, where reviewed: the member,
   * called at them, runs no client code beyond callbacks whose own
   * signatures state the same effect, and writes no location the call did not
   * allocate. A stated signature's own effect overrides it. */
  effect?: Effect;
};
type Effect = CallEffect;
/** A reviewed replacement signature of an overlay entry. */
type StatedSignature = { receiver?: TypeTerm; params: TypeTerm[]; result: TypeTerm; effect?: Effect };
/** A stated signature with its own effect. */
type EffectSignature = { params: TypeTerm[]; result: TypeTerm; effect: Effect };

const at: [number, number] = [0, 0];
const atomOf = (name: "string" | "number" | "undefined" | "unknown" | "boolean" | "null" | "bigint" | "symbol"): TypeTerm => ({ k: "atom", name, span: at });
const optionalNumber: TypeTerm = { k: "union", parts: [atomOf("number"), atomOf("undefined")], span: at };
/** `locales`, as the host reads it without running client code: a tag, or a
 * readonly array of tags read by index; a malformed tag is a `RangeError`. */
const locales: TypeTerm = { k: "union", span: at, parts: [atomOf("string"),
  { k: "array", presence: "dense", readonly: true, element: atomOf("string"), span: at }, atomOf("undefined")] };

// Native conversion of a primitive runs no client code. This is a bound on
// the receiver's element type, not a claim that a readonly alias is immutable.
const primitiveElements: TypeTerm = { k: "union", span: at, parts:
  [atomOf("string"), atomOf("number"), atomOf("boolean"), atomOf("null"),
   atomOf("undefined"), atomOf("bigint"), atomOf("symbol")] };
/** A regular recursive native contract, not a depth-limited tree of arrays. */
const stringConvertibleIdentity: DeclarationIdentity =
  { module: "tscert/array-conversion", name: "StringConvertible", span: [0, 0] };
const stringConvertible: TypeTerm = { k: "reference", args: [], span: at,
  reference: { name: "StringConvertible", span: at, arguments: [], target: stringConvertibleIdentity } };
const element: TypeTerm = { k: "binder", name: "T", span: at };
const maybeElement: TypeTerm = { k: "union", parts: [element, atomOf("undefined")], span: at };
const arrayOf = (value: TypeTerm, readonly: boolean, presence: ArrayPresence = "readable"): TypeTerm =>
  ({ k: "array", presence, readonly, element: value, span: at });
const callback = (value: TypeTerm, result: TypeTerm,
    effect: CallEffect, presence: ArrayPresence = "readable"): TypeTerm =>
  ({ k: "function", effect, receiver: null, rest: null, span: at,
     params: [value, atomOf("number"), arrayOf(element, true, presence)], result });
/** `find` and `findIndex` visit every index below the length they read
 * first, present or not. At a callback that changes no array store, the
 * receiver's store, and so its length, stays as it was, and each visit reads
 * an element at the receiver's contract; at any other, a store may shrink
 * (`grow` may drop indices past a hole), and a visit past the new length
 * passes `undefined`. */
const findCallback = (effect: CallEffect, footprint: ClosedFootprint): TypeTerm =>
  callback(footprint.store === "keep" ? element : maybeElement, atomOf("unknown"), effect);
const mappedElement: TypeTerm = { k: "binder", name: "U", span: at };
/** The predicates `every` and `map` state an elements fact at, each with the
 * type of the values it admits (`CallEffects.ElemPred`). */
const elementPredicates: readonly { kind: ElementKind; type: TypeTerm }[] = [
  { kind: "string", type: atomOf("string") }, { kind: "number", type: atomOf("number") },
  { kind: "boolean", type: atomOf("boolean") },
];
const guarded: TypeTerm = { k: "binder", name: "S", span: at };
/** A destructive member's: within `{value: any, store: keep}` but for its
 * receiver's store, which it may change arbitrarily. */
const receiverStoreEffect: CallEffect = { ...footprintEffect({ value: "any", store: "keep" }), receiverStore: true };
/** `sort`'s at a comparator whose store changes are at most `grow`: its
 * writeback grows the receiver's store over the whole call (`sort_grow`) and
 * changes element contents. */
const sortGrowEffect: CallEffect = footprintEffect({ value: "any", store: "grow" });
/** The closed footprints that keep an array's dense prefixes: those whose
 * change to array stores is at most `grow` (`stableDenseClosed`), smallest
 * first. */
const stableForDensity = closedFootprints.filter((f) => f.store !== "any");
/** A callback member's signatures, one per closed footprint `ε`: called at a
 * callback within `ε`, the member is within `ε`, since besides the callback
 * it reads the receiver and allocates only its result. */
const atEachFootprint = (signature: (effect: CallEffect, footprint: ClosedFootprint) =>
    { params: TypeTerm[]; result: TypeTerm }, fresh: boolean = false): EffectSignature[] =>
  closedFootprints.map((footprint) => {
    const effect = footprintEffect(footprint);
    return { ...signature(effect, footprint), effect: { ...effect, fresh } };
  });

export const overlay: readonly OverlayEntry[] = [
  // `forEach` reads the length once and the present elements, data
  // properties, and writes nothing beside its callback's calls, as `every`
  // below: within the callback's footprint.
  { name: "forEach", from: "ReadonlyArray",
    signature: "forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, thisArg?: any): void;",
    stated: atEachFootprint((effect) => ({ params: [callback(element, atomOf("unknown"), effect)],
      result: atomOf("undefined") })) },
  { name: "map", from: "ReadonlyArray",
    signature: "map<U>(callbackfn: (value: T, index: number, array: readonly T[]) => U, thisArg?: any): U[];",
    // `map` relies on every index below the length it captured staying
    // present until it tests it. A callback whose footprint changes array
    // stores at most by `grow` keeps that fact (FOOTPRINTS.md, "Natives":
    // `map_rely`, `denseCheck_stable`), so at each such footprint a dense
    // receiver gives a dense result, and the call's own footprint is the
    // callback's: `map` reads the receiver and allocates its result, a fresh
    // array, whose store its result is (each signature states it). Any
    // other callback gives a result that may hold holes. These are ordinary
    // per-signature call contracts.
    stated: [
      ...stableForDensity.map((footprint) => ({
        receiver: arrayOf(element, true, "dense"),
        params: [callback(element, mappedElement, footprintEffect(footprint))],
        result: arrayOf(mappedElement, false), effect: { ...footprintEffect(footprint), fresh: true } })),
      { params: [callback(element, mappedElement, ordinaryEffect)],
        result: arrayOf(mappedElement, false, "sparse"), effect: { ...ordinaryEffect, fresh: true } },
      // At a receiver whose present elements all have the predicate's kind
      // when the call starts (`requires`), and a callback within the empty
      // footprint, every element `map` passes has it: the callback changes
      // no location, so the store and each element keep their contents
      // between visits (`elems_rely`), and `map` passes only present
      // elements, skipping a hole and leaving it in its fresh result. So the
      // callback is called at the predicate's type; the result's presence
      // is the receiver's.
      ...elementPredicates.flatMap(({ kind, type }) => [
        { receiver: arrayOf(element, true, "dense"), params: [callback(type, mappedElement, emptyEffect)],
          result: arrayOf(mappedElement, false), effect: { ...emptyEffect, fresh: true, requires: [kind] } },
        { params: [callback(type, mappedElement, emptyEffect)],
          result: arrayOf(mappedElement, false, "sparse"), effect: { ...emptyEffect, fresh: true, requires: [kind] } },
      ]),
    ] },
  // `flatMap` calls the callback at each position still present when
  // visited, below the length read before the first call, and appends the
  // present elements of each array it returns, in order, to a fresh array:
  // the result holds no hole whatever the callback does. A result that is
  // no array is appended as it is, and one that is an array is flattened,
  // so the declared `U | ReadonlyArray<U>` is unsound where `U` admits an
  // array (`U := number[]` with a callback returning `[x]` gives numbers at
  // `number[]`). Stated at a callback returning an array, whose holes are
  // skipped; `thisArg` is not stated, so a call must omit it. The sparse
  // receiver signature also passes a sparse array as the callback's third
  // argument: visiting a present entry does not establish other entries.
  { name: "flatMap", from: "ReadonlyArray",
    signature: "flatMap<U, This = undefined>(\n" +
      "        callback: (this: This, value: T, index: number, array: T[]) => U | ReadonlyArray<U>,\n" +
      "        thisArg?: This,\n" +
      "    ): U[];",
    unbound: ["This"],
    stated: [
      ...atEachFootprint((effect) => ({ params: [callback(element, arrayOf(mappedElement, true, "sparse"), effect, "sparse")],
        result: arrayOf(mappedElement, false) }), true).map(signature =>
          ({ ...signature, receiver: arrayOf(element, true, "sparse") })),
    ] },
  // Only the overload with an initial value. The one without, `reduce(cb)`,
  // is a second signature of the member beside the generic `reduce<U>`,
  // and a prototype member is read as one scheme with one signature
  // (SOURCE-CONTRACTS.md, "Prototype contracts"). Its throw on an empty
  // array is no reason: a throw is an outcome (SOURCE-MODEL.md, "Throws").
  { name: "reduce", from: "ReadonlyArray",
    signature: "reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  { name: "reduceRight", from: "ReadonlyArray",
    signature: "reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  // These callbacks run only for properties still present when visited.
  // find/findIndex below instead visit every index in the original range.
  // Beside each callback's call, the member reads the length once, tests and
  // reads the receiver's own numeric keys, data properties (`numericOwn`),
  // and `filter` defines the kept elements on a fresh array (ordinary
  // construction), whose store its result is: it runs no other client code
  // and writes no existing location. So at a callback within a footprint the
  // member is: a signature per closed footprint; `thisArg` is not stated.
  // At a guard within the empty footprint promising a predicate's type,
  // `every` visits every element present when it is called, each keeping
  // its contents until it returns, and answers `true` only where the guard
  // answered `true` of each: a guard's answer is a Boolean, which `every`'s
  // test reads as itself. So a `true` result leaves every present element
  // of the receiver of the guard's type (`elements`, `native-guard-every`).
  { name: "every", from: "ReadonlyArray",
    signature: "every(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    stated: [
      ...atEachFootprint((effect) => ({ params: [callback(element, atomOf("unknown"), effect)],
        result: atomOf("boolean") })),
      ...elementPredicates.map(({ kind, type }) => ({
        params: [callback(element, type, { ...emptyEffect, promise: { guards: { param: 0 } } })],
        result: atomOf("boolean"), effect: { ...emptyEffect, elements: [kind] } })),
    ] },
  { name: "some", from: "ReadonlyArray",
    signature: "some(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    // `some` visits only present positions, including on a sparse receiver.
    // Its third callback argument is that same array and retains its holes.
    stated: atEachFootprint((effect) => ({ params: [callback(element, atomOf("unknown"), effect, "sparse")],
        result: atomOf("boolean") })).map(signature =>
          ({ ...signature, receiver: arrayOf(element, true, "sparse") })) },
  // `filter` is reviewed against its guard overload, whose declaration binds
  // `S`, and states both of TypeScript's: the predicate one at each
  // footprint, and the guard one at a callback promising `S` of the value it
  // is passed (`native-guard-filter`). The native appends the very value it
  // passed where the answer is `true`, which the promise leaves an `S`, and
  // type membership survives every write the callbacks after it make; so
  // the result holds `S`s, without the bound `S extends T`. The callback is
  // at the top footprint, which every promise signature's footprint is
  // within, and so is the call. A sparse receiver is tested for presence
  // before each visit too; its callback's third argument stays sparse.
  { name: "filter", from: "ReadonlyArray",
    signature: "filter<S extends T>(predicate: (value: T, index: number, array: readonly T[]) => value is S, thisArg?: any): S[];",
    stated: [
      ...atEachFootprint((effect) => ({ params: [callback(element, atomOf("unknown"), effect)],
        result: arrayOf(element, false) }), true),
      { params: [callback(element, guarded, promiseEffect(false, 0))], result: arrayOf(guarded, false),
        effect: { ...ordinaryEffect, fresh: true } },
      ...atEachFootprint((effect) => ({ params: [callback(element, atomOf("unknown"), effect, "sparse")],
        result: arrayOf(element, false) }), true).map((signature) =>
          ({ ...signature, receiver: arrayOf(element, true, "sparse") })),
      { receiver: arrayOf(element, true, "sparse"),
        params: [callback(element, guarded, promiseEffect(false, 0), "sparse")], result: arrayOf(guarded, false),
        effect: { ...ordinaryEffect, fresh: true } },
    ] },
  // `flat()`, at its default depth 1, visits the receiver's present
  // elements below the length it read first and, for each array, appends
  // that array's present elements, as they are, to a fresh array (ordinary
  // construction): the result holds no hole, and an element is flattened
  // one level only, whatever its own type. Stated at a receiver of arrays,
  // where each element of the result is an element of one of them; `depth`
  // is not stated, so a call must omit it. The receiver's elements are read
  // as `IsArray` and the arrays' own data properties; it runs no client code
  // and writes no existing location.
  { name: "flat", from: "ReadonlyArray",
    signature: "flat<A, D extends number = 1>(\n" +
      "        this: A,\n" +
      "        depth?: D,\n" +
      "    ): FlatArray<A, D>[];",
    binders: ["U"],
    stated: [{ receiver: arrayOf(arrayOf(mappedElement, true, "sparse"), true, "sparse"), params: [],
      result: arrayOf(mappedElement, false, "dense"), effect: { ...emptyEffect, fresh: true } }] },
  // The members below, through `at`, read the receiver's elements, convert
  // only numbers (an index, a bound) and, for `join` and `toString`,
  // elements meeting the standard conversion contract, compare by strict
  // equality or SameValueZero, and allocate only their result: they run no
  // client code and write no existing location.
  { name: "slice", from: "ReadonlyArray", signature: "slice(start?: number, end?: number): T[];",
    effect: { ...emptyEffect, fresh: true } },
  { name: "join", from: "ReadonlyArray", signature: "join(separator?: string): string;",
    bounds: new Map([["T", stringConvertible]]), effect: emptyEffect,
    // Get at a missing numeric key yields undefined, converted to empty text.
    // Present elements meet the same conversion bound as a readable array.
    stated: [
      { receiver: arrayOf(element, true, "sparse"), params: [], result: atomOf("string") },
      { receiver: arrayOf(element, true, "sparse"),
        params: [{ k: "union", parts: [atomOf("string"), atomOf("undefined")], span: at }], result: atomOf("string") }] },
  { name: "toString", from: "ReadonlyArray", signature: "toString(): string;",
    bounds: new Map([["T", stringConvertible]]), effect: emptyEffect },
  { name: "indexOf", from: "ReadonlyArray",
    signature: "indexOf(searchElement: T, fromIndex?: number): number;", effect: emptyEffect },
  { name: "lastIndexOf", from: "ReadonlyArray",
    signature: "lastIndexOf(searchElement: T, fromIndex?: number): number;", effect: emptyEffect },
  { name: "includes", from: "ReadonlyArray",
    signature: "includes(searchElement: T, fromIndex?: number): boolean;", effect: emptyEffect },
  { name: "at", from: "ReadonlyArray", signature: "at(index: number): T | undefined;",
    effect: emptyEffect },
  // `find` is reviewed against its guard overload, whose declaration binds
  // `S`, and states both of TypeScript's: the predicate one at each
  // footprint, and the guard one at each footprint keeping array stores
  // (`native-guard-find`). There every visit passes an element at the
  // receiver's contract, and where the answer is `true` the native returns
  // that very value, which the promise leaves an `S`, running no client code
  // after the callback's call; where none answers `true`, `undefined`.
  { name: "find", from: "ReadonlyArray",
    signature: "find<S extends T>(predicate: (value: T, index: number, obj: readonly T[]) => value is S, thisArg?: any): S | undefined;",
    stated: [
      ...atEachFootprint((effect, footprint) => ({ params: [findCallback(effect, footprint)],
        result: maybeElement })),
      ...closedFootprints.filter((footprint) => footprint.store === "keep").map((footprint) => ({
        params: [callback(element, guarded, { ...footprintEffect(footprint), promise: { guards: { param: 0 } } })],
        result: { k: "union", parts: [guarded, atomOf("undefined")], span: at } satisfies TypeTerm,
        effect: footprintEffect(footprint) })),
    ] },
  { name: "findIndex", from: "ReadonlyArray",
    signature: "findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): number;",
    stated: atEachFootprint((effect, footprint) => ({ params: [findCallback(effect, footprint)],
      result: atomOf("number") })) },
  // Mutators take a mutable array.
  { name: "sort", from: "Array",
    signature: "sort(compareFn?: (a: T, b: T) => number): this;",
    // These are independent call contracts, not a restriction on every T.
    // An explicit comparator avoids element coercion. Omitted/undefined
    // comparison instead requires the recursive standard-conversion view.
    // Beside its comparator's calls, `sort` reads the length and the present
    // elements, data properties, calls the comparator only on the values it
    // snapshot, converts its numeric answer, and writes back to its own
    // receiver: `Set` of each index below the snapshot's count, then `Delete`
    // of each later one, changing only the receiver's store and element
    // contents. At a comparator whose store changes are at most `grow`, the
    // receiver's store changes by `grow` over the whole call (`sort_grow`),
    // so the call is within `{value: any, store: grow}`: a signature per
    // such footprint of the comparator. At any other it states no footprint.
    stated: [
      ...stableForDensity.map((footprint) => ({
        params: [{ k: "function", effect: footprintEffect(footprint), receiver: null, params: [element, element],
          rest: null, result: atomOf("number"), span: at } satisfies TypeTerm],
        result: arrayOf(element, false), effect: sortGrowEffect })),
      { params: [{ k: "function", effect: ordinaryEffect, receiver: null, params: [element, element], rest: null,
          result: atomOf("number"), span: at }],
        result: { k: "array", presence: "readable", readonly: false, element, span: at } },
      { receiver: { k: "intersection", parts: [
          { k: "array", presence: "readable", readonly: false, element, span: at },
          { k: "array", presence: "readable", readonly: true, element: stringConvertible, span: at }], span: at },
        params: [atomOf("undefined")], result: { k: "array", presence: "readable", readonly: false, element, span: at } },
    ] },
  // Footprints (SOURCE-CONTRACTS.md, "Native footprints"): `push` and
  // `unshift` change the receiver's store by `grow` and only element
  // contents beside it; `pop`, `shift` and `reverse` change the receiver's
  // store arbitrarily and only element contents beside it: within
  // `{value: any, store: keep}` but for the receiver's store
  // (`receiverStore`); `sort` grows it over the whole call when its
  // comparator's store changes do. The store relations are proved of the
  // specification steps (FootprintNatives.lean); that each native changes
  // nothing but its store and element contents is this entry's audit.
  { name: "push", from: "Array", signature: "push(...items: T[]): number;",
    effect: footprintEffect({ value: "any", store: "grow" }) },
  { name: "pop", from: "Array", signature: "pop(): T | undefined;", effect: receiverStoreEffect },
  { name: "shift", from: "Array", signature: "shift(): T | undefined;", effect: receiverStoreEffect },
  { name: "unshift", from: "Array", signature: "unshift(...items: T[]): number;",
    effect: footprintEffect({ value: "any", store: "grow" }) },
  { name: "reverse", from: "Array", signature: "reverse(): T[];", effect: receiverStoreEffect },
  // `splice` without items: it converts only numbers, copies the present
  // elements of the deleted range to a fresh array (ordinary construction),
  // holes where the receiver has them, so its result is read as the
  // receiver's elements are, then moves or deletes each later index and sets
  // the length: it changes the receiver's store arbitrarily and allocates its
  // result. The overload with `items` is not listed.
  { name: "splice", from: "Array", signature: "splice(start: number, deleteCount?: number): T[];",
    effect: { ...receiverStoreEffect, fresh: true } },
  // Iteration: `ArrayIterator<T>` extends `IteratorObject<T,
  // BuiltinIteratorReturn, unknown>`, an `Iterator<T, BuiltinIteratorReturn,
  // unknown>`, which meets `Iterator<T>`, the result `Iterable<T>` asks for.
  { name: "[Symbol.iterator]", from: "ReadonlyArray",
    signature: "[Symbol.iterator](): ArrayIterator<T>;", resultAs: "Iterator", effect: emptyEffect },
  // `values` is the same function as `[Symbol.iterator]`; `keys` and
  // `entries` are iterators of the same kind (CreateArrayIterator), each step
  // reading the receiver's current length (its own data property) and, for
  // `entries`, its element at the index as `[Symbol.iterator]`'s does,
  // yielding the index or a fresh pair (CreateArrayFromList). Each call
  // allocates a fresh iterator and runs no code. The result is read as an
  // `IterableIterator`: the iterator is its own (`%IteratorPrototype%`'s
  // `[Symbol.iterator]` returns it), and a loop steps it by the iterator
  // protocol, its chain holding no `return` (DESIGN.md, "Trust surface").
  { name: "values", from: "ReadonlyArray", signature: "values(): ArrayIterator<T>;", resultAs: "IterableIterator",
    effect: emptyEffect },
  { name: "keys", from: "ReadonlyArray", signature: "keys(): ArrayIterator<number>;", resultAs: "IterableIterator",
    effect: emptyEffect },
  { name: "entries", from: "ReadonlyArray", signature: "entries(): ArrayIterator<[number, T]>;",
    resultAs: "IterableIterator", effect: emptyEffect },
  // Not listed: `concat` names `ConcatArray`.
];


/** The members of the primitive wrappers' prototypes. Each is an own property
 * of that prototype (so `String.prototype.toLocaleString`, which is
 * `Object.prototype`'s, is not listed). A member that throws on some
 * arguments (`repeat(-1)`) is read as declared; one whose declaration admits
 * a `RegExp` is stated at the strings (`split`, `replace`); members only a
 * `RegExp` or an `any` callback serves (`match`, `search`, `replace` with a
 * replacer) are not listed. `locales` is stated at a string or a readonly
 * array of strings, read by index; `options`, an `Intl` interface whose
 * values the host converts, running an object's own `toString`, is dropped,
 * so a call must omit it. A string owns `length` and its indices, which are
 * not the prototype's. */
const primitiveOverlay: Readonly<Record<string, readonly OverlayEntry[]>> &
  Readonly<Record<PrimitiveKind, readonly OverlayEntry[]>> = {
  string: [
    { name: "toString", from: "String", signature: "toString(): string;" },
    { name: "valueOf", from: "String", signature: "valueOf(): string;" },
    { name: "charAt", from: "String", signature: "charAt(pos: number): string;" },
    { name: "charCodeAt", from: "String", signature: "charCodeAt(index: number): number;" },
    { name: "concat", from: "String", signature: "concat(...strings: string[]): string;" },
    { name: "indexOf", from: "String", signature: "indexOf(searchString: string, position?: number): number;" },
    { name: "lastIndexOf", from: "String",
      signature: "lastIndexOf(searchString: string, position?: number): number;" },
    { name: "localeCompare", from: "String", signature: "localeCompare(that: string): number;" },
    { name: "slice", from: "String", signature: "slice(start?: number, end?: number): string;" },
    { name: "substring", from: "String", signature: "substring(start: number, end?: number): string;" },
    { name: "toLowerCase", from: "String", signature: "toLowerCase(): string;" },
    { name: "toUpperCase", from: "String", signature: "toUpperCase(): string;" },
    { name: "trim", from: "String", signature: "trim(): string;" },
    { name: "includes", from: "String", signature: "includes(searchString: string, position?: number): boolean;" },
    { name: "startsWith", from: "String",
      signature: "startsWith(searchString: string, position?: number): boolean;" },
    { name: "endsWith", from: "String", signature: "endsWith(searchString: string, endPosition?: number): boolean;" },
    // Any other form is a `RangeError`, an outcome: the overload taking any
    // string, or none, is read.
    { name: "normalize", from: "String", signature: "normalize(form?: string): string;" },
    // A negative or infinite count is a `RangeError`.
    { name: "repeat", from: "String", signature: "repeat(count: number): string;" },
    // With a string pattern, the host reads no `[Symbol.split]` or
    // `[Symbol.replace]` of the client's (a string primitive's lookup ends at
    // `String.prototype`, which has none), and `$` patterns in a string
    // replacement are string operations. A `RegExp`, and a replacer
    // callback, are not stated. `split` gives a fresh array of strings,
    // whose store its result is; `replaceAll` of a non-global `RegExp` would
    // throw.
    { name: "split", from: "String", signature: "split(separator: string | RegExp, limit?: number): string[];",
      effect: { ...emptyEffect, fresh: true },
      stated: [{ params: [atomOf("string"), optionalNumber],
        result: { k: "array", presence: "dense", readonly: false, element: atomOf("string"), span: at } }] },
    { name: "replace", from: "String", signature: "replace(searchValue: string | RegExp, replaceValue: string): string;",
      stated: [{ params: [atomOf("string"), atomOf("string")], result: atomOf("string") }] },
    { name: "replaceAll", from: "String",
      signature: "replaceAll(searchValue: string | RegExp, replaceValue: string): string;",
      stated: [{ params: [atomOf("string"), atomOf("string")], result: atomOf("string") }] },
    { name: "codePointAt", from: "String", signature: "codePointAt(pos: number): number | undefined;" },
    { name: "trimStart", from: "String", signature: "trimStart(): string;" },
    { name: "trimEnd", from: "String", signature: "trimEnd(): string;" },
    // The pad is a string; a length past the host's string limit is a
    // `RangeError`.
    { name: "padStart", from: "String", signature: "padStart(targetLength: number, padString?: string): string;" },
    { name: "padEnd", from: "String", signature: "padEnd(targetLength: number, padString?: string): string;" },
    { name: "at", from: "String", signature: "at(index: number): string | undefined;" },
  ],
  number: [
    // Each throws a `RangeError` outside 2..36 radixes, 0..100 digits, 1..100
    // precision: an outcome, not a wrong value.
    { name: "toString", from: "Number", signature: "toString(radix?: number): string;" },
    { name: "valueOf", from: "Number", signature: "valueOf(): number;" },
    { name: "toFixed", from: "Number", signature: "toFixed(fractionDigits?: number): string;" },
    { name: "toExponential", from: "Number", signature: "toExponential(fractionDigits?: number): string;" },
    { name: "toPrecision", from: "Number", signature: "toPrecision(precision?: number): string;" },
    { name: "toLocaleString", from: "Number",
      signature: "toLocaleString(locales?: string | string[], options?: Intl.NumberFormatOptions): string;",
      stated: [{ params: [locales], result: atomOf("string") }] },
  ],
  bigint: [
    { name: "toString", from: "BigInt", signature: "toString(radix?: number): string;" },
    { name: "valueOf", from: "BigInt", signature: "valueOf(): bigint;" },
    { name: "toLocaleString", from: "BigInt",
      signature: "toLocaleString(locales?: Intl.LocalesArgument, options?: BigIntToLocaleStringOptions): string;",
      stated: [{ params: [locales], result: atomOf("string") }] },
  ],
  boolean: [
    { name: "valueOf", from: "Boolean", signature: "valueOf(): boolean;" },
    // TypeScript reads it from `Object`; `Boolean.prototype` owns it.
    { name: "toString", from: "Object", signature: "toString(): string;" },
  ],
};

/** Standard library interfaces read through the overlay rather than as
 * declared (SOURCE-CONTRACTS.md, "Prototype contracts"): a reference to
 * `Set<T>`, `Map<K, V>` or `Date` is the interface with only the members
 * listed, each a host-relative method on the object it is read from (its
 * prototype's, at run time), a property a readonly view. Every other member,
 * overload and base is left out, which gives a supertype of the declared
 * interface. A `this` result is the receiver (`resultIsReceiver`), the
 * interface at its own parameters, which the library's declared methods do
 * return. `thisArg` is dropped, as for arrays.
 *
 * The host's collections hold their elements in internal slots the model
 * does not see; a method's contract is what it returns. `Set<T>` and
 * `Map<K, V>` are invariant in their parameters, since `add` and `set` take
 * them and `has`, `get` and `forEach` give them. `keys`, `values` and
 * `entries` give a `SetIterator` or `MapIterator`, read as an `Iterator` of
 * its argument. Not listed: `[Symbol.toStringTag]`. Of `Date`, the getters,
 * `setTime`, `valueOf`, `toString` and `toISOString` (a `RangeError` for an
 * invalid date, an outcome); `[Symbol.toPrimitive]`, whose overloads take
 * hints, is not listed, nor the members taking locales.
 *
 * The readers state the empty footprint: `has` and `get` compare by
 * SameValueZero and run no code, `keys`, `values`, `entries` and
 * `[Symbol.iterator]` allocate a fresh iterator, and `Date`'s getters,
 * `valueOf`, `toString` and `toISOString` read its time value. The members
 * that change a collection or a date (`add`, `set`, `delete`, `clear`,
 * `setTime`) state `{value: any, store: keep}`: they compare keys by
 * SameValueZero or take a number, run no code, and write only the receiver's
 * internal slots, which hold values and no array store. `forEach`, which
 * calls its callback, states none (SOURCE-CONTRACTS.md, "Native
 * footprints"). */
const changesValues = footprintEffect({ value: "any", store: "keep" });
export const interfaceOverlay: Map<string, readonly OverlayEntry[]> = new Map<string, readonly OverlayEntry[]>([
  ["Set", [
    { name: "add", from: "Set", signature: "add(value: T): this;", resultIsReceiver: true, effect: changesValues },
    { name: "clear", from: "Set", signature: "clear(): void;", effect: changesValues },
    { name: "delete", from: "Set", signature: "delete(value: T): boolean;", effect: changesValues },
    { name: "forEach", from: "Set",
      signature: "forEach(callbackfn: (value: T, value2: T, set: Set<T>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    { name: "has", from: "Set", signature: "has(value: T): boolean;", effect: emptyEffect },
    { name: "size", from: "Set", signature: "readonly size: number;" },
    // A host collection's tag, which its prototype holds: no object the
    // fragment builds has one (a literal or class writes no well-known
    // symbol key but `Symbol.iterator`), so none passes for a host `Set`,
    // whose iteration is the host's (`%Iterate:Set%`).
    { name: "[Symbol.toStringTag]", from: "Set", signature: "readonly [Symbol.toStringTag]: string;" },
    // As for arrays: `SetIterator<T>` is an `Iterator<T>`.
    { name: "[Symbol.iterator]", from: "Set", signature: "[Symbol.iterator](): SetIterator<T>;",
      resultAs: "NativeIterator", effect: emptyEffect },
    // A `SetIterator<T>` is read as an `Iterator<T>` too; a `for...of` over
    // one steps it as the host's (`intrinsics.mts`).
    { name: "keys", from: "Set", signature: "keys(): SetIterator<T>;", resultAs: "NativeIterator", effect: emptyEffect },
    { name: "values", from: "Set", signature: "values(): SetIterator<T>;", resultAs: "NativeIterator", effect: emptyEffect },
    { name: "entries", from: "Set", signature: "entries(): SetIterator<[T, T]>;", resultAs: "NativeIterator", effect: emptyEffect },
  ]],
  // Results describe normal returns. Native set throws TypeError for keys
  // other than objects and non-registered symbols; get/has/delete return
  // undefined/false for those keys. The declared K limits admitted calls.
  ["WeakMap", [
    { name: "get", from: "WeakMap", signature: "get(key: K): V | undefined;", effect: emptyEffect },
    { name: "has", from: "WeakMap", signature: "has(key: K): boolean;", effect: emptyEffect },
    { name: "set", from: "WeakMap", signature: "set(key: K, value: V): this;", resultIsReceiver: true,
      effect: changesValues },
    { name: "delete", from: "WeakMap", signature: "delete(key: K): boolean;", effect: changesValues },
    { name: "[Symbol.toStringTag]", from: "WeakMap", signature: "readonly [Symbol.toStringTag]: string;" },
  ]],
  ["Map", [
    { name: "clear", from: "Map", signature: "clear(): void;", effect: changesValues },
    { name: "delete", from: "Map", signature: "delete(key: K): boolean;", effect: changesValues },
    { name: "forEach", from: "Map",
      signature: "forEach(callbackfn: (value: V, key: K, map: Map<K, V>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    // TypeScript's own `V | undefined`: a key the map lacks reads nothing.
    { name: "get", from: "Map", signature: "get(key: K): V | undefined;", effect: emptyEffect },
    { name: "has", from: "Map", signature: "has(key: K): boolean;", effect: emptyEffect },
    { name: "set", from: "Map", signature: "set(key: K, value: V): this;", resultIsReceiver: true,
      effect: changesValues },
    { name: "size", from: "Map", signature: "readonly size: number;" },
    { name: "[Symbol.toStringTag]", from: "Map", signature: "readonly [Symbol.toStringTag]: string;" },
    { name: "[Symbol.iterator]", from: "Map", signature: "[Symbol.iterator](): MapIterator<[K, V]>;",
      resultAs: "NativeIterator", effect: emptyEffect },
    { name: "keys", from: "Map", signature: "keys(): MapIterator<K>;", resultAs: "NativeIterator", effect: emptyEffect },
    { name: "values", from: "Map", signature: "values(): MapIterator<V>;", resultAs: "NativeIterator", effect: emptyEffect },
    { name: "entries", from: "Map", signature: "entries(): MapIterator<[K, V]>;", resultAs: "NativeIterator", effect: emptyEffect },
  ]],
  // The readers' views of a `Set` and a `Map`, read through the overlay as
  // `ReadonlyArray` is through `ArrayProto`, at the restriction of the
  // collection's own readers (`thisArg` dropped, `[Symbol.iterator]`'s
  // result read as an `Iterator`, and `keys`', `values`' and `entries'` as
  // an `IterableIterator`, its own `[Symbol.iterator]` kept, which the native
  // collection iterator meets), so that a `Set<T>` is a `ReadonlySet<T>` and
  // a `Map<K, V>` a `ReadonlyMap<K, V>`. A program's object may meet these
  // interfaces, which state no `[Symbol.toStringTag]`: each member keeps the
  // effect its declaration states, and an iteration runs the iterator
  // protocol (`iterationKind` in `declaration-graph.mts` picks it for a call
  // of `keys`, `values` or `entries`).
  ["ReadonlySet", [
    { name: "forEach", from: "ReadonlySet",
      signature: "forEach(callbackfn: (value: T, value2: T, set: ReadonlySet<T>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    { name: "has", from: "ReadonlySet", signature: "has(value: T): boolean;" },
    { name: "size", from: "ReadonlySet", signature: "readonly size: number;" },
    { name: "[Symbol.iterator]", from: "ReadonlySet", signature: "[Symbol.iterator](): SetIterator<T>;",
      resultAs: "Iterator" },
    { name: "keys", from: "ReadonlySet", signature: "keys(): SetIterator<T>;", resultAs: "IterableIterator" },
    { name: "values", from: "ReadonlySet", signature: "values(): SetIterator<T>;", resultAs: "IterableIterator" },
    { name: "entries", from: "ReadonlySet", signature: "entries(): SetIterator<[T, T]>;", resultAs: "IterableIterator" },
  ]],
  ["ReadonlyMap", [
    { name: "forEach", from: "ReadonlyMap",
      signature: "forEach(callbackfn: (value: V, key: K, map: ReadonlyMap<K, V>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    { name: "get", from: "ReadonlyMap", signature: "get(key: K): V | undefined;" },
    { name: "has", from: "ReadonlyMap", signature: "has(key: K): boolean;" },
    { name: "size", from: "ReadonlyMap", signature: "readonly size: number;" },
    { name: "[Symbol.iterator]", from: "ReadonlyMap", signature: "[Symbol.iterator](): MapIterator<[K, V]>;",
      resultAs: "Iterator" },
    { name: "keys", from: "ReadonlyMap", signature: "keys(): MapIterator<K>;", resultAs: "IterableIterator" },
    { name: "values", from: "ReadonlyMap", signature: "values(): MapIterator<V>;", resultAs: "IterableIterator" },
    { name: "entries", from: "ReadonlyMap", signature: "entries(): MapIterator<[K, V]>;", resultAs: "IterableIterator" },
  ]],
  ["Date", [
    ...["valueOf", "getTime", "getFullYear", "getUTCFullYear", "getMonth", "getUTCMonth", "getDate",
      "getUTCDate", "getDay", "getUTCDay", "getHours", "getUTCHours", "getMinutes", "getUTCMinutes",
      "getSeconds", "getUTCSeconds", "getMilliseconds", "getUTCMilliseconds", "getTimezoneOffset"]
      .map((name): OverlayEntry => ({ name, from: "Date", signature: `${name}(): number;`, effect: emptyEffect })),
    { name: "setTime", from: "Date", signature: "setTime(time: number): number;", effect: changesValues },
    ...["toString", "toISOString"]
      .map((name): OverlayEntry => ({ name, from: "Date", signature: `${name}(): string;`, effect: emptyEffect })),
  ]],
]);

/** The native collection iterator `NativeCollectionIterator<T>`, what a
 * `Set`'s or a `Map`'s `keys`, `values`, `entries` and `[Symbol.iterator]`
 * return: the library's `IterableIterator<T>`, its `[Symbol.iterator]`
 * `%IteratorPrototype%`'s, which returns the iterator, marked by `[⟨CollectionIterator⟩]:
 * undefined`, a key no source declaration, literal or class states. So only
 * those members give a value of it, and the host iteration intrinsic
 * `%Iterate:Iterator%`, which steps it as the built-in iterator does,
 * requires it: an `Iterator<T>` of any other source, a `ReadonlySet`'s
 * included, runs the iterator protocol or is refused there. */
export const collectionIteratorMark: DeclarationIdentity =
  { module: "tscert/collections", name: "CollectionIterator", span: [0, 0] };
export const nativeCollectionIteratorIdentity: DeclarationIdentity =
  { module: "tscert/collections", name: "NativeCollectionIterator", span: [0, 0] };
export function nativeCollectionIteratorDefinition(mark: number,
    iterator: (element: TypeTerm) => TypeTerm): TypeDefinition {
  return { declaration: nativeCollectionIteratorIdentity, bases: [],
    parameters: [{ name: "T", span: [0, 0], defaulted: false }],
    expression: { k: "intersection", span: [0, 0], parts: [iterator({ k: "parameter", index: 0, span: [0, 0] }),
      { k: "object", stringIndex: null, calls: [], span: [0, 0], fields: [{ name: { symbol: mark },
        optional: false, readonly: true, type: { k: "atom", name: "undefined", span: [0, 0] }, span: [0, 0] }] }] } };
}
/** The native collection iterator over `element`. */
export const nativeCollectionIterator = (element: TypeTerm): TypeTerm => ({ k: "reference", args: [element],
  span: [0, 0], reference: { name: nativeCollectionIteratorIdentity.name, span: [0, 0], arguments: [[0, 0]],
    target: nativeCollectionIteratorIdentity } });

/** The reading view of a host collection, `NativeSetView<T>` and
 * `NativeMapView<K, V>`: the members of the `Set<T>` and `Map<K, V>`
 * overlays above that take no element, `[Symbol.toStringTag]`, `size`,
 * `[Symbol.iterator]`, `keys`, `values` and `entries`, each as the overlay
 * reads it. So a `Set<T>` is a `NativeSetView<T>` and a `Map<K, V>` a
 * `NativeMapView<K, V>`, by width; the view is covariant in its parameters,
 * since it states no member taking one, and a value of it is written
 * nothing through it. Only a host collection meets it, as only one meets
 * the overlay: its iterators are the marked native collection iterator,
 * which no source value is, and its tag a well-known symbol key no object
 * the fragment builds writes. It is the parameter of `%Iterate:Set%` and
 * `%Iterate:Map%` and what `%InstanceOf:Set%` and `%InstanceOf:Map%`
 * promise of an operand answering `true` (`intrinsics.mts`). */
export type CollectionKind = "Set" | "Map";
export const nativeCollectionViewIdentity = (kind: CollectionKind): DeclarationIdentity =>
  ({ module: "tscert/collections", name: `Native${kind}View`, span: [0, 0] });
/** The keys the view reads by, the well-known symbols `Symbol.iterator`
 * and `Symbol.toStringTag`, by their indices among the listed symbols. */
export type CollectionViewKeys = { iterator: number; toStringTag: number };
export function nativeCollectionViewDefinition(kind: CollectionKind, keys: CollectionViewKeys,
    iterator: (element: TypeTerm) => TypeTerm): TypeDefinition {
  const span: [number, number] = [0, 0];
  const parameter = (index: number): TypeTerm => ({ k: "parameter", index, span });
  const pair = (first: TypeTerm, second: TypeTerm): TypeTerm =>
    ({ k: "tuple", presence: "dense", readonly: false, required: [first, second], optional: [], rest: null, span });
  // The elements each iterator steps through: a `Set`'s values, its entries
  // `[v, v]`; a `Map`'s entries `[k, v]`, its keys and its values.
  const [element, keyed, valued, entry]: [TypeTerm, TypeTerm, TypeTerm, TypeTerm] = kind === "Set"
    ? [parameter(0), parameter(0), parameter(0), pair(parameter(0), parameter(0))]
    : [pair(parameter(0), parameter(1)), parameter(0), parameter(1), pair(parameter(0), parameter(1))];
  const method = (name: PropertyKey, result: TypeTerm) => ({ name, optional: false, readonly: false, span,
    type: { k: "function", effect: emptyEffect, receiver: { k: "self", span }, params: [], rest: null,
      result: iterator(result), span } satisfies TypeTerm });
  const property = (name: PropertyKey, type: "string" | "number") =>
    ({ name, optional: false, readonly: true, type: { k: "atom", name: type, span } satisfies TypeTerm, span });
  return { declaration: nativeCollectionViewIdentity(kind), bases: [],
    parameters: (kind === "Set" ? ["T"] : ["K", "V"]).map(name => ({ name, span, defaulted: false })),
    expression: { k: "object", stringIndex: null, calls: [], span, fields: [
      property({ symbol: keys.toStringTag }, "string"), property("size", "number"),
      method({ symbol: keys.iterator }, element), method("keys", keyed), method("values", valued),
      method("entries", entry)] } };
}
/** The view of a host collection at its arguments. */
export const nativeCollectionView = (kind: CollectionKind, args: TypeTerm[]): TypeTerm => {
  const identity = nativeCollectionViewIdentity(kind);
  return { k: "reference", args, span: [0, 0], reference: { name: identity.name, span: [0, 0],
    arguments: args.map((): [number, number] => [0, 0]), target: identity } };
};

/** What the overlay reads through the declaration graph: the symbol a
 * computed key names, and a reference to a standard library interface, which
 * then joins the graph. */
export type OverlayLibrary = {
  symbol: (written: ts.PropertyAccessExpression | ts.Identifier) => number;
  /** Identity from the standard library, never a synthetic identifier node. */
  wellKnownSymbol: (name: string) => number | null;
  reference: (node: ts.InterfaceDeclaration, args: TypeTerm[], span: [number, number]) => TypeTerm;
  /** Whether a file is one of the standard library's, by the compiler's own
   * library resolution. */
  libraryFile: (file: ts.SourceFile) => boolean;
  reviewed: ReviewedReader;
};

/** Read `body`, an interface's binders and members (`<T> { ... }`), as the
 * compiler parses an interface declaration of it: the overlay's reviewed
 * signatures, which the project's library may not declare. Only the syntax is
 * read, inside `read`. */
export type ReviewedReader = <R>(body: string, read: (declaration: ts.InterfaceDeclaration) => R) => R;

/** The synthetic declaration the array types' prototype view names. */
const arrayProtoIdentity: DeclarationIdentity =
  { module: "tscert/array-prototype", name: "ArrayProto", span: [0, 0] };

/** A primitive whose members are read through its wrapper's prototype. */
export type PrimitiveKind = "string" | "number" | "bigint" | "boolean";
export const primitiveKinds: readonly PrimitiveKind[] = ["string", "number", "bigint", "boolean"];
const wrapperName: Record<PrimitiveKind, string> =
  { string: "String", number: "Number", bigint: "BigInt", boolean: "Boolean" };

/** The synthetic declaration of a primitive's prototype contract, and the
 * module value holding the built-in prototype at it, a name no source
 * identifier spells. */
const primitiveProtoIdentity = (kind: PrimitiveKind): DeclarationIdentity =>
  ({ module: `tscert/${kind}-prototype`, name: `${wrapperName[kind]}Proto`, span: [0, 0] });
export const primitivePrototypeName = (kind: PrimitiveKind): string =>
  `[[${wrapperName[kind]}.prototype]]`;

/** One prototype's contract: its declaration, its own binders (the array's
 * element `T`), and the receiver a member declared on an interface takes. */
type Prototype = {
  identity: DeclarationIdentity;
  binders: string[];
  receiver: (from: string) => TypeTerm;
  entries: readonly OverlayEntry[];
  /** The effect a member's signatures state where its entry states none:
   * the empty footprint where every listed member, at each signature the
   * overlay reads, runs no client code and writes no location the call did
   * not allocate. */
  effect: Effect;
};

/** `ArrayProto` as a declaration: a record of readonly members, each a scheme
 * over the array's element binder `T` and the member's own binders, whose one
 * signature takes the array as its receiver. `at` locates a refusal. */
export function arrayPrototype(checker: Checker, at: Node, library: OverlayLibrary,
    entries: readonly OverlayEntry[] = overlay): TypeDefinition[] {
  const element: TypeTerm = { k: "binder", name: "T", span: [0, 0] };
  const result = prototype(checker, at, library, { identity: arrayProtoIdentity, binders: ["T"], entries,
    effect: ordinaryEffect,
    receiver: from => ({ k: "array", presence: "readable", readonly: from === "ReadonlyArray", element, span: [0, 0] }) });
  if (!entries.some(e => ["join", "toString", "sort"].includes(e.name))) return [result];
  const hook = library.wellKnownSymbol("toPrimitive");
  if (result.expression?.k !== "object") throw Error("a prototype contract must be an object");
  // Standard Array.prototype has no conversion hook. The optional undefined
  // view states this, and the existing array own-key invariant prevents an
  // array from shadowing it, toString or join. External arrays obey it too.
  if (hook !== null) result.expression.fields.push({ name: { symbol: hook }, optional: true,
    readonly: true, type: atomOf("undefined"), span: [0, 0] });
  const conversion: TypeDefinition = { declaration: stringConvertibleIdentity, parameters: [], bases: [],
    expression: hook === null ? primitiveElements : { k: "union", span: [0, 0], parts:
      [primitiveElements, arrayOf(stringConvertible, true)] } };
  return [result, conversion];
}

/** A primitive's prototype contract, `StringProto` for `String.prototype`: a
 * record of readonly members, each of whose signatures takes the primitive
 * as its receiver. */
/** The non-empty string literals written in the separator of a `split`
 * call of `source` that passes no limit. Which literals are collected bounds
 * only which calls the non-empty form serves: the form holds at any union of
 * non-empty separators. */
export function splitSeparators(source: Node): string[] {
  const found = new Set<string>();
  const literals = (n: Node): void => {
    if ((ts.isStringLiteral(n) || ts.isNoSubstitutionTemplateLiteral(n)) && n.text !== "") found.add(n.text);
    n.forEachChild(literals);
  };
  const visit = (n: Node): void => {
    if (ts.isCallExpression(n) && n.arguments.length === 1 && ts.isPropertyAccessExpression(n.expression) &&
        n.expression.name.text === "split") {
      const [separator] = n.arguments;
      if (separator) literals(separator);
    }
    n.forEachChild(visit);
  };
  visit(source);
  return [...found].sort();
}

/** `split` at a union of non-empty string separators and no limit returns at
 * least one element (SOURCE-CONTRACTS.md, "a non-empty `split`"): ECMA-262's
 * `split` returns `[S]` where the separator does not occur, and `[]` only for
 * a limit whose `ToUint32` is 0 or an empty receiver at an empty separator. */
const nonEmptySplit = (separators: readonly string[]): { params: TypeTerm[]; result: TypeTerm }[] => separators.length ? [{
  params: [{ k: "union", span: at, parts: separators.map((text): TypeTerm => ({ k: "literal", name: "string", text, span: at })) }],
  result: { k: "tuple", presence: "dense", readonly: false, optional: [], span: at,
    required: [atomOf("string")], rest: atomOf("string") } }] : [];

export function primitivePrototype(checker: Checker, at: Node, library: OverlayLibrary,
    kind: PrimitiveKind, separators: readonly string[] = [],
    entries: readonly OverlayEntry[] = primitiveOverlay[kind]): TypeDefinition {
  // A string's own keys are its `length` and its indices: never the prototype's.
  const owned = entries.find(e => kind === "string" && (e.name === "length" || /^\d/.test(e.name)));
  if (owned) throw Error(`a string owns '${owned.name}'; String.prototype's does not answer for it`);
  entries = entries.map(e => kind === "string" && e.name === "split" && e.stated
    ? { ...e, stated: [...nonEmptySplit(separators), ...e.stated] } : e);
  return prototype(checker, at, library, { identity: primitiveProtoIdentity(kind), binders: [], entries,
    effect: emptyEffect, receiver: () => ({ k: "atom", name: kind, span: [0, 0] }) });
}

/** `FunctionProto`, the contract of `Function.prototype` a function's
 * `toString` is read from: `toString` alone, at the receiver `Function`.
 * ECMA-262's `Function.prototype.toString` (20.2.3.5) returns a string for a
 * callable receiver (its source text, or a `NativeFunction` string), reads no
 * property and calls no code, and throws a `TypeError` on any other receiver,
 * an outcome: the empty footprint. A function's lookup of `toString` reaches
 * it where the function owns no `toString` and no object of its chain before
 * `Function.prototype` holds one: the program's functions own none
 * (SOURCE-CONTRACTS.md, "Function.prototype.toString"), and external code's
 * are assumed to (DESIGN.md, "Trust surface"). */
const functionOverlay: readonly OverlayEntry[] =
  [{ name: "toString", from: "Function", signature: "toString(): string;" }];
const functionProtoIdentity: DeclarationIdentity =
  { module: "tscert/function-prototype", name: "FunctionProto", span: [0, 0] };
export const functionPrototypeName = "[[Function.prototype]]";

export function functionPrototype(checker: Checker, at: Node, library: OverlayLibrary,
    entries: readonly OverlayEntry[] = functionOverlay): TypeDefinition {
  return prototype(checker, at, library, { identity: functionProtoIdentity, binders: [], entries,
    effect: emptyEffect, receiver: () => ({ k: "callable", span: [0, 0] }) });
}

/** The interface declarations `name` resolves to. */
function interfacesOf(checker: Checker, name: Node): ts.InterfaceDeclaration[] {
  return (checker.getSymbolAtLocation(name)?.declarations ?? []).map(d => d.resolve())
    .filter((n): n is ts.InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
}

/** The refusal of a merge `mergeRefusal` reports into the interface `name`. */
export const mergeMessage = (name: string, refusal: string): string =>
  `${name} is not the standard library's alone: a declaration merges ${refusal} into it, ` +
  `which the standard library's ${name} does not declare at that contract`;

/** The overlay entries reviewing the members of the standard library
 * interface `name`, from every prototype's overlay. An `Array` is read at
 * `ArrayProto`, whose members `ReadonlyArray` declares too. */
function reviewedEntries(name: string): OverlayEntry[] {
  const from = name === "Array" ? ["Array", "ReadonlyArray"] : [name];
  return [overlay, ...Object.values(primitiveOverlay), ...interfaceOverlay.values()]
    .flatMap(entries => entries.filter(entry => from.includes(entry.from)));
}

/** A merge into an interface: what it merges that the reviewed contract
 * does not state (`refusal`, `null` where nothing), and the members it
 * states that the reviewed contract does (`admitted`).
 *
 * Every value of the interface is read at TScert's reviewed interpretation
 * of the host's prototype, the overlay. A merged declaration (a global
 * augmentation, or a base it adds) states a member of every value of the
 * type, and a merge installs nothing at run time; so each member it gives the
 * interface must be one the overlay reviews at the same contract, which the
 * reviewed translation, its corrections and effects included, then
 * represents; any other would be erased. Node's `at` polyfill
 * (`RelativeIndexable<T>`) states the reviewed `at`; a `toJSON` stating that
 * every array holds a hook is no member the overlay reviews. Contracts are
 * compared as the TypeTerm reader reads them, the merged declaration and the
 * overlay's reviewed signature alike: the interfaces' binders by position, a
 * base at the arguments each heritage path gives it, a member's own binders
 * by position with their bounds, its optionality, and each declaration of an
 * overloaded member on its own; a parameter's name is no part of it. A form
 * the reader does not read here (a named type, a computed key, a call,
 * construct or index signature, a base outside the merge) is refused. */
export function mergeRefusal(checker: Checker, libraryFile: (file: ts.SourceFile) => boolean,
    parts: readonly ts.InterfaceDeclaration[], reviewed: ReviewedReader):
    { refusal: string | null; admitted: ReadonlySet<string> } {
  const isLibrary = (node: Node): boolean => libraryFile(node.getSourceFile());
  const none = { refusal: null, admitted: new Set<string>() };
  if (parts.every(isLibrary)) return none;
  type Member = ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration;
  type Binders = Map<string, TypeTerm>;
  const positional = (part: ts.InterfaceDeclaration): Binders => new Map((part.typeParameters ?? [])
    .map((p, i): [string, TypeTerm] => [p.name.text, { k: "binder", name: `$${i}`, span: [0, 0] }]));
  class Unread extends Error {}
  const scopeOf = (node: Node, binders: Binders, own: readonly string[] = []): TermScope => ({
    source: node.getSourceFile(),
    annotation: false,
    fail: (_node, message) => { throw new Unread(message); },
    named: (reference, span) => {
      if (ts.isIdentifier(reference.typeName) && !reference.typeArguments?.length) {
        const index = own.indexOf(reference.typeName.text);
        if (index >= 0) return { k: "binder", name: `#${index}`, span };
        const bound = binders.get(reference.typeName.text);
        if (bound) return bound;
      }
      throw new Unread("a named type");
    },
  });
  // A contract without its spans: the reader keeps no parameter name, so
  // equal contracts read alike.
  type ContractData = null | undefined | boolean | number | string
    | readonly ContractData[] | { readonly [key: string]: ContractData };
  const isArrayData = (value: ContractData): value is readonly ContractData[] => Array.isArray(value);
  const canonical = (value: ContractData): string => {
    if (Array.isArray(value)) {
      // The native test excludes arrays on the other branch; this checked
      // guard retains their element contract under the shadow declarations.
      if (!isArrayData(value)) throw Error("array data tests disagree");
      const items: readonly ContractData[] = value;
      return `[${items.map(canonical).join(",")}]`;
    }
    if (value !== null && typeof value === "object")
      return `{${Object.entries(value).filter(([key]: [string, ContractData]) => key !== "span")
        .map(([key, field]: [string, ContractData]) => `${key}:${canonical(field)}`).join(",")}}`;
    return typeof value === "string" ? JSON.stringify(value) : String(value);
  };
  const contract = (member: Member, binders: Binders): string | null => {
    try {
      const own = ts.isMethodSignatureDeclaration(member) ? member.typeParameters ?? [] : [];
      if (own.some(p => p.defaultType)) return null;
      const scope = scopeOf(member, binders, own.map(p => p.name.text));
      const shape = ts.isMethodSignatureDeclaration(member)
        ? { k: "method", optional: member.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
            bounds: own.map(p => p.constraint ? typeTerm(scope, p.constraint) : null),
            forms: signatures(scope, member.parameters, member.type, member, [0, 0]) }
        : { k: "property", optional: member.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
            readonly: !!member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword),
            type: typeTerm(scope, member.type, member) };
      return canonical(shape);
    } catch (error) {
      if (error instanceof Unread) return null;
      throw error;
    }
  };
  const nameOf = (member: Member): string | null => ts.isIdentifier(member.name) ? member.name.text : null;
  const merged: { member: Member; binders: Binders }[] = [];
  // Each declaration once at each substitution: a base two heritage paths
  // reach at different arguments is read at both. TypeScript refuses a
  // circular base, and the bound keeps the walk finite regardless.
  const seen = new Map<ts.InterfaceDeclaration, Set<string>>();
  let visits = 0;
  const visit = (part: ts.InterfaceDeclaration, binders: Binders): string | null => {
    const at = canonical([...binders.entries()]);
    const known = seen.get(part) ?? new Set<string>();
    if (known.has(at)) return null;
    known.add(at);
    seen.set(part, known);
    if (++visits > 256) return "a chain of bases the reader does not bound";
    for (const member of part.members) {
      if (!ts.isMethodSignatureDeclaration(member) && !ts.isPropertySignatureDeclaration(member))
        return "a call, construct or index signature";
      if (nameOf(member) === null) return "a member at a computed key";
      merged.push({ member, binders });
    }
    for (const clause of part.heritageClauses ?? [])
      for (const base of clause.types) {
        const bases = interfacesOf(checker, base.expression);
        if (!ts.isIdentifier(base.expression) || !bases.length || bases.some(isLibrary))
          return "a base outside the merge";
        let args: TypeTerm[];
        try {
          const scope = scopeOf(part, binders);
          args = (base.typeArguments ?? []).map(t => typeTerm(scope, t));
        } catch (error) {
          if (error instanceof Unread) return "a base at arguments the reader does not read";
          throw error;
        }
        for (const declaration of bases) {
          const substitution = new Map<string, TypeTerm>();
          for (const [index, parameter] of (declaration.typeParameters ?? []).entries()) {
            const argument = args[index];
            if (!argument) return "a base at arguments the reader does not read";
            substitution.set(parameter.name.text, argument);
          }
          if (substitution.size !== args.length) return "a base at arguments the reader does not read";
          const refused = visit(declaration, substitution);
          if (refused) return refused;
        }
      }
    return null;
  };
  for (const part of parts) {
    if (isLibrary(part)) continue;
    const refused = visit(part, positional(part));
    if (refused) return { refusal: refused, admitted: new Set() };
  }
  if (!merged.length) return none;
  // The overlay's reviewed signatures, read as one interface over the
  // library declaration's binders.
  const entries = reviewedEntries(parts[0]?.name.text ?? "");
  const library = parts.find(isLibrary);
  const binderList = (library?.typeParameters ?? []).map(p => p.name.text).join(", ");
  const contracts = entries.length && library
    ? reviewed(`${binderList ? `<${binderList}>` : ""} {\n${entries.map(e => e.signature).join("\n")}\n}`,
        declaration => declaration.members
          .filter((m): m is Member => ts.isMethodSignatureDeclaration(m) || ts.isPropertySignatureDeclaration(m))
          .flatMap(m => {
            const name = nameOf(m);
            const stated = contract(m, positional(declaration));
            return name !== null && stated !== null ? [`${name} ${stated}`] : [];
          }))
    : [];
  const admitted = new Set<string>();
  for (const { member, binders } of merged) {
    const name = nameOf(member);
    const stated = contract(member, binders);
    if (name === null || stated === null || !contracts.includes(`${name} ${stated}`))
      return { refusal: `'${name}'`, admitted: new Set() };
    admitted.add(name);
  }
  return { refusal: null, admitted };
}

function prototype(checker: Checker, at: Node, library: OverlayLibrary, proto: Prototype): TypeDefinition {
  const declared = (name: string) => {
    const symbol = checker.resolveName(name, SymbolFlags.Interface, at, false);
    const parts = (symbol?.declarations ?? []).map(d => d.resolve())
      .filter((n): n is ts.InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
    if (!parts.length) throw Error(`the standard library declares no ${name}`);
    return parts;
  };
  // The interfaces the contract reads, each with the standard library's
  // bases its declarations name, are validated once (`mergeRefusal`).
  const validated = new Set<ts.InterfaceDeclaration>();
  // The members a merge states at the reviewed contract, by interface.
  const admitted = new Map<string, ReadonlySet<string>>();
  const standard = (parts: readonly ts.InterfaceDeclaration[]): void => {
    const [first] = parts;
    if (!first || validated.has(first)) return;
    validated.add(first);
    const merge = mergeRefusal(checker, library.libraryFile, parts, library.reviewed);
    if (merge.refusal) throw Error(mergeMessage(first.name.text, merge.refusal));
    admitted.set(first.name.text, merge.admitted);
    // A merged part's bases are the merge's, which `mergeRefusal` reads.
    for (const part of parts.filter(p => library.libraryFile(p.getSourceFile())))
      for (const clause of part.heritageClauses ?? [])
        for (const base of clause.types) standard(interfacesOf(checker, base.expression));
  };
  const libraries = new Map<string, ts.InterfaceDeclaration[]>();
  const libraryOf = (name: string) => {
    const known = libraries.get(name);
    if (known) return known;
    const parts = declared(name);
    standard(parts);
    libraries.set(name, parts);
    return parts;
  };
  const interfaceOf = (name: "Iterator" | "IterableIterator") => {
    const parts = declared(name);
    standard(parts);
    const [first] = parts;
    if (!first) throw Error(`the standard library declares no ${name}`);
    return first;
  };

  const fields = proto.entries.flatMap(entry => {
    // The reviewed declaration is the library's: a merged one is validated
    // by its contract (`mergeRefusal`), never selected by its spelling.
    const named = libraryOf(entry.from).filter(part => library.libraryFile(part.getSourceFile()))
      .flatMap(part => part.members
        .filter(ts.isMethodSignatureDeclaration)
        .filter(m => (ts.isIdentifier(m.name) ? m.name.text : m.name.getText(part.getSourceFile())) === entry.name)
        .map(m => ({ member: m, source: part.getSourceFile() })));
    if (!named.length) {
      // A member the project's standard library does not declare, as `at`
      // before ES2022, is part of the prototype where a merge states it at
      // the reviewed contract: read from the reviewed signature.
      if (!admitted.get(entry.from)?.has(entry.name)) return [];
      return library.reviewed(` {\n${entry.signature}\n}`, declaration => {
        const [member] = declaration.members;
        if (!member || !ts.isMethodSignatureDeclaration(member) || !ts.isIdentifier(member.name))
          throw Error(`${entry.from}.${entry.name}: its reviewed signature is no method`);
        return field(entry, member, member.getSourceFile());
      });
    }
    const found = named.filter(({ member, source }) =>
      member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length)
      throw Error(`${entry.from}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    return field(entry, only.member, only.source);
  });
  return { declaration: proto.identity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: [], span: [0, 0] } };

  /** The prototype's field of `entry`, read from its declaration `member`. */
  function field(entry: OverlayEntry, member: ts.MethodSignatureDeclaration, source: ts.SourceFile):
      Extract<TypeTerm, { k: "object" }>["fields"] {
    // The library's own result interface (`ArrayIterator<T>`), read as
    // `Iterator<T>`, is validated with its chain as the contract's.
    if (entry.resultAs && library.libraryFile(source) && member.type && ts.isTypeReferenceNode(member.type))
      standard(interfacesOf(checker, member.type.typeName));
    const span: [number, number] = [0, 0];
    const own = entry.binders ?? (member.typeParameters ?? []).map(p => p.name.text)
      .filter(name => !entry.unbound?.includes(name));
    // The member's own binders lead, as its declaration lists them, so an
    // explicit type argument list instantiates them in order; the
    // prototype's binders follow, fixed by the receiver.
    const binders = [...own, ...proto.binders];
    const scope: TermScope = {
      source,
      annotation: false,
      fail: (_node, message) => { throw Error(`${message} in ${entry.from}.${entry.name}`); },
      named: (node, pos) => {
        if (ts.isIdentifier(node.typeName) && binders.includes(node.typeName.text) &&
            !node.typeArguments?.length)
          return { k: "binder", name: node.typeName.text, span: pos };
        throw Error(`${entry.from}.${entry.name} names a type the overlay does not read`);
      },
    };
    const receiver = proto.receiver(entry.from);
    const nameOf = (p: ts.ParameterDeclaration) => ts.isIdentifier(p.name) ? p.name.text : "";
    const parameters = member.parameters.filter(p => !entry.drop?.includes(nameOf(p)));
    // The weaker result: the interface at the declared result's one argument
    // (`[number, T]` of `entries(): ArrayIterator<[number, T]>`).
    const resultArgument = (): TypeTerm => {
      const declared = member.type;
      const [argument, ...others] = declared && ts.isTypeReferenceNode(declared) ? declared.typeArguments ?? [] : [];
      if (!argument || others.length) throw Error(`${entry.from}.${entry.name} has no element type to state`);
      return typeTerm(scope, argument, member);
    };
    // A prototype's iterator is no collection's: its result is a library interface.
    if (entry.resultAs === "NativeIterator") throw Error(`${entry.from}.${entry.name}: a prototype states no collection iterator`);
    const stated = entry.result ?? (entry.resultAs
      ? library.reference(interfaceOf(entry.resultAs), [resultArgument()], span)
      : entry.resultIsReceiver ? receiver : undefined);
    const forms = entry.stated
      ? entry.stated.map(f => ({ k: "function", effect: f.effect ?? entry.effect ?? proto.effect, receiver: f.receiver ?? null,
          params: f.params, rest: null, result: f.result,
          span } satisfies Extract<TypeTerm, { k: "function" }>))
      : signatures(scope, parameters, entry.resultAs ? undefined : member.type, member, span, false, stated)
          .map(f => ({ ...f, effect: entry.effect ?? proto.effect }));
    const [first] = forms;
    if (!first)
      throw Error(`${entry.from}.${entry.name} requires a nonempty supported signature family`);
    // Several forms of a member without binders are their intersection
    // (`split`'s non-empty form beside its general one).
    const type: TypeTerm = binders.length
      ? { k: "scheme", binders: binders.map(name => ({ name, bound: entry.bounds?.get(name) ?? null, resolution: null, default: null, span })),
          signatures: forms.map(f => ({ ...f, receiver: f.receiver ?? receiver })), span }
      : oneTerm(forms.map(f => ({ ...f, receiver: f.receiver ?? receiver })), span);
    const key = ts.isComputedPropertyName(member.name) &&
        (ts.isPropertyAccessExpression(member.name.expression) || ts.isIdentifier(member.name.expression))
      ? { symbol: library.symbol(member.name.expression) } : entry.name;
    return [{ name: key, optional: false, readonly: true, type, span }];
  }
}
