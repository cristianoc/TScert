/** The contracts of the built-in prototypes a program reads members through:
 * `ArrayProto`, the contract of `Array.prototype`, and `StringProto`,
 * `NumberProto`, `BigIntProto` and `BooleanProto`, those of the prototypes a
 * primitive's members are read from (`"a".toUpperCase()`, `n.toString(16)`).
 * Each is TypeScript's own declarations, as the project's standard library
 * states them (`ReadonlyArray<T>` and `Array<T>`; `String`, `Number`, `BigInt`,
 * `Boolean`), through a reviewed overlay. Nothing is vendored. The overlay
 * holds only what those declarations leave out and soundness needs
 * (DESIGN.md, "Trust surface"; PROGRAM-TYPING.md, "Prototype contracts"):
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
 * throw is an outcome, never a wrong value (DESIGN.md, "Throws").
 *
 * Each entry records the declaration text it was reviewed against. A member
 * is read only from a declaration with exactly that text, so a changed
 * library is refused here and reviewed again, never trusted silently. */
import { SymbolFlags, type Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ArrayPresence } from "./type-graph.mts";
import type { Node } from "typescript/unstable/ast";
import { signatures, type TermScope } from "./type-term.mts";
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";

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
  /** The declared `this` result is the receiver. */
  resultIsReceiver?: boolean;
  /** The result stated as this standard library interface at `T`, which the
   * declared result implies: a weaker contract than the declaration's. */
  resultAs?: "Iterator";
  /** A reviewed restriction on a quantified parameter. Required when native
   * coercion could otherwise call an arbitrary client method. */
  bounds?: Readonly<Record<string, TypeTerm>>;
  /** A reviewed result contract replacing TypeScript's result. In particular,
   * map may produce holes and cannot promise a dense array. */
  result?: TypeTerm;
  /** A reviewed replacement signature: restrict implicit client hooks (e.g.
   * split on strings only), or correct explicit callback arguments (find
   * visits missing positions with undefined). The receiver is the prototype's. */
  stated?: { receiver?: TypeTerm; params: TypeTerm[]; result: TypeTerm; effect?: Effect }[];
  /** The effect the member's signatures state, where reviewed: the member,
   * called at them, runs no client code beyond callbacks whose own
   * signatures state the same effect, and writes no location the call did not
   * allocate. A stated signature's own effect overrides it. */
  effect?: Effect;
};
type Effect = "unrestricted" | "preservesInputHeap";

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
    effect: "unrestricted" | "preservesInputHeap"): TypeTerm =>
  ({ k: "function", effect, receiver: null, rest: null, span: at,
     params: [value, atomOf("number"), arrayOf(element, true)], result });
const findingCallback = callback(maybeElement, atomOf("unknown"), "unrestricted");
const preservingFind = callback(element, atomOf("unknown"), "preservesInputHeap");
const mappedElement: TypeTerm = { k: "binder", name: "U", span: at };

export const overlay: readonly OverlayEntry[] = [
  // At a callback preserving the input heap, `forEach` does, as `every`
  // below: it reads the length once and the present elements, data
  // properties, and writes nothing.
  { name: "forEach", from: "ReadonlyArray",
    signature: "forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, thisArg?: any): void;",
    stated: [{ params: [callback(element, atomOf("unknown"), "preservesInputHeap")], result: atomOf("undefined"),
        effect: "preservesInputHeap" },
      { params: [callback(element, atomOf("unknown"), "unrestricted")], result: atomOf("undefined") }] },
  { name: "map", from: "ReadonlyArray",
    signature: "map<U>(callbackfn: (value: T, index: number, array: readonly T[]) => U, thisArg?: any): U[];",
    // Under ordinary construction, a callback preserving the input heap
    // leaves every original source position present throughout traversal.
    // The unrestricted contract admits reentrancy and only promises presence
    // at visited positions. Both are ordinary per-signature call contracts.
    stated: [
      { receiver: arrayOf(element, true, "dense"), params: [callback(element, mappedElement, "preservesInputHeap")],
        result: arrayOf(mappedElement, false), effect: "preservesInputHeap" },
      { params: [callback(element, mappedElement, "unrestricted")],
        result: arrayOf(mappedElement, false, "sparse") },
    ] },
  // `flatMap` calls the callback at each position still present when
  // visited, below the length read before the first call, and appends the
  // present elements of each array it returns, in order, to a fresh array:
  // the result holds no hole whatever the callback does. A result that is
  // no array is appended as it is, and one that is an array is flattened,
  // so the declared `U | ReadonlyArray<U>` is unsound where `U` admits an
  // array (`U := number[]` with a callback returning `[x]` gives numbers at
  // `number[]`). Stated at a callback returning an array, whose holes are
  // skipped; `thisArg` is not stated, so a call must omit it.
  { name: "flatMap", from: "ReadonlyArray",
    signature: "flatMap<U, This = undefined>(\n" +
      "        callback: (this: This, value: T, index: number, array: T[]) => U | ReadonlyArray<U>,\n" +
      "        thisArg?: This,\n" +
      "    ): U[];",
    unbound: ["This"],
    stated: [{ params: [callback(element, arrayOf(mappedElement, true, "sparse"), "unrestricted")],
      result: arrayOf(mappedElement, false) }] },
  // Only the overload with an initial value. The one without, `reduce(cb)`,
  // is a second signature of the member beside the generic `reduce<U>`,
  // and a prototype member is read as one scheme with one signature
  // (PROGRAM-TYPING.md, "Prototype contracts"). Its throw on an empty
  // array is no reason: a throw is an outcome (DESIGN.md, "Throws").
  { name: "reduce", from: "ReadonlyArray",
    signature: "reduce<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  { name: "reduceRight", from: "ReadonlyArray",
    signature: "reduceRight<U>(callbackfn: (previousValue: U, currentValue: T, currentIndex: number, array: readonly T[]) => U, initialValue: U): U;" },
  // These callbacks run only for properties still present when visited.
  // find/findIndex below instead visit every index in the original range.
  // Beside each callback's call, the member reads the length once, tests and
  // reads the receiver's own numeric keys, data properties (`numericOwn`),
  // and `filter` defines the kept elements on a fresh array (ordinary
  // construction): it runs no other client code and writes no existing
  // location. So at a callback preserving the input heap the member does,
  // a signature of its own beside the declared one; `thisArg` is not stated.
  { name: "every", from: "ReadonlyArray",
    signature: "every(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    stated: [{ params: [preservingFind], result: atomOf("boolean"), effect: "preservesInputHeap" },
      { params: [callback(element, atomOf("unknown"), "unrestricted")], result: atomOf("boolean") }] },
  { name: "some", from: "ReadonlyArray",
    signature: "some(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;",
    stated: [{ params: [preservingFind], result: atomOf("boolean"), effect: "preservesInputHeap" },
      { params: [callback(element, atomOf("unknown"), "unrestricted")], result: atomOf("boolean") }] },
  { name: "filter", from: "ReadonlyArray",
    signature: "filter(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): T[];",
    stated: [{ params: [preservingFind], result: arrayOf(element, false), effect: "preservesInputHeap" },
      { params: [callback(element, atomOf("unknown"), "unrestricted")], result: arrayOf(element, false) }] },
  // The members below, through `at`, read the receiver's elements, convert
  // only numbers (an index, a bound) and, for `join` and `toString`,
  // elements meeting the standard conversion contract, compare by strict
  // equality or SameValueZero, and allocate only their result: they run no
  // client code and write no existing location.
  { name: "slice", from: "ReadonlyArray", signature: "slice(start?: number, end?: number): T[];",
    effect: "preservesInputHeap" },
  { name: "join", from: "ReadonlyArray", signature: "join(separator?: string): string;",
    bounds: { T: stringConvertible }, effect: "preservesInputHeap" },
  { name: "toString", from: "ReadonlyArray", signature: "toString(): string;",
    bounds: { T: stringConvertible }, effect: "preservesInputHeap" },
  { name: "indexOf", from: "ReadonlyArray",
    signature: "indexOf(searchElement: T, fromIndex?: number): number;", effect: "preservesInputHeap" },
  { name: "lastIndexOf", from: "ReadonlyArray",
    signature: "lastIndexOf(searchElement: T, fromIndex?: number): number;", effect: "preservesInputHeap" },
  { name: "includes", from: "ReadonlyArray",
    signature: "includes(searchElement: T, fromIndex?: number): boolean;", effect: "preservesInputHeap" },
  { name: "at", from: "ReadonlyArray", signature: "at(index: number): T | undefined;",
    effect: "preservesInputHeap" },
  { name: "find", from: "ReadonlyArray",
    signature: "find(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): T | undefined;",
    stated: [{ params: [preservingFind], result: maybeElement, effect: "preservesInputHeap" },
      { params: [findingCallback], result: maybeElement }] },
  { name: "findIndex", from: "ReadonlyArray",
    signature: "findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): number;",
    stated: [{ params: [preservingFind], result: atomOf("number"), effect: "preservesInputHeap" },
      { params: [findingCallback], result: atomOf("number") }] },
  // Mutators take a mutable array.
  { name: "sort", from: "Array",
    signature: "sort(compareFn?: (a: T, b: T) => number): this;",
    // These are independent call contracts, not a restriction on every T.
    // An explicit comparator avoids element coercion. Omitted/undefined
    // comparison instead requires the recursive standard-conversion view.
    stated: [
      { params: [{ k: "function", effect: "unrestricted", receiver: null, params: [element, element], rest: null,
          result: atomOf("number"), span: at }],
        result: { k: "array", presence: "readable", readonly: false, element, span: at } },
      { receiver: { k: "intersection", parts: [
          { k: "array", presence: "readable", readonly: false, element, span: at },
          { k: "array", presence: "readable", readonly: true, element: stringConvertible, span: at }], span: at },
        params: [atomOf("undefined")], result: { k: "array", presence: "readable", readonly: false, element, span: at } },
    ] },
  { name: "push", from: "Array", signature: "push(...items: T[]): number;" },
  { name: "pop", from: "Array", signature: "pop(): T | undefined;" },
  { name: "shift", from: "Array", signature: "shift(): T | undefined;" },
  { name: "unshift", from: "Array", signature: "unshift(...items: T[]): number;" },
  { name: "reverse", from: "Array", signature: "reverse(): T[];" },
  // Iteration: `ArrayIterator<T>` extends `IteratorObject<T,
  // BuiltinIteratorReturn, unknown>`, an `Iterator<T, BuiltinIteratorReturn,
  // unknown>`, which meets `Iterator<T>`, the result `Iterable<T>` asks for.
  { name: "[Symbol.iterator]", from: "ReadonlyArray",
    signature: "[Symbol.iterator](): ArrayIterator<T>;", resultAs: "Iterator", effect: "preservesInputHeap" },
  // Not listed: `concat` names `ConcatArray`, and `values`, `keys` and
  // `entries` are not needed yet.
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
const primitiveOverlay: Readonly<Record<PrimitiveKind, readonly OverlayEntry[]>> = {
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
    // callback, are not stated. `split` gives a fresh array of strings;
    // `replaceAll` of a non-global `RegExp` would throw.
    { name: "split", from: "String", signature: "split(separator: string | RegExp, limit?: number): string[];",
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
 * declared (PROGRAM-TYPING.md, "Prototype contracts"): a reference to
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
 * The readers state `preservesInputHeap`: `has` and `get` compare by
 * SameValueZero and run no code, `keys`, `values`, `entries` and
 * `[Symbol.iterator]` allocate a fresh iterator, and `Date`'s getters,
 * `valueOf`, `toString` and `toISOString` read its time value. The members
 * that change a collection or a date, and `forEach`, which calls its
 * callback, state none. */
export const interfaceOverlay: Readonly<Record<string, readonly OverlayEntry[]>> = {
  Set: [
    { name: "add", from: "Set", signature: "add(value: T): this;", resultIsReceiver: true },
    { name: "clear", from: "Set", signature: "clear(): void;" },
    { name: "delete", from: "Set", signature: "delete(value: T): boolean;" },
    { name: "forEach", from: "Set",
      signature: "forEach(callbackfn: (value: T, value2: T, set: Set<T>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    { name: "has", from: "Set", signature: "has(value: T): boolean;", effect: "preservesInputHeap" },
    { name: "size", from: "Set", signature: "readonly size: number;" },
    // A host collection's tag, which its prototype holds: no object the
    // fragment builds has one (a literal or class writes no well-known
    // symbol key but `Symbol.iterator`), so none passes for a host `Set`,
    // whose iteration is the host's (`%Iterate:Set%`).
    { name: "[Symbol.toStringTag]", from: "Set", signature: "readonly [Symbol.toStringTag]: string;" },
    // As for arrays: `SetIterator<T>` is an `Iterator<T>`.
    { name: "[Symbol.iterator]", from: "Set", signature: "[Symbol.iterator](): SetIterator<T>;",
      resultAs: "Iterator", effect: "preservesInputHeap" },
    // A `SetIterator<T>` is read as an `Iterator<T>` too; a `for...of` over
    // one steps it as the host's (`intrinsics.mts`).
    { name: "keys", from: "Set", signature: "keys(): SetIterator<T>;", resultAs: "Iterator", effect: "preservesInputHeap" },
    { name: "values", from: "Set", signature: "values(): SetIterator<T>;", resultAs: "Iterator", effect: "preservesInputHeap" },
    { name: "entries", from: "Set", signature: "entries(): SetIterator<[T, T]>;", resultAs: "Iterator", effect: "preservesInputHeap" },
  ],
  Map: [
    { name: "clear", from: "Map", signature: "clear(): void;" },
    { name: "delete", from: "Map", signature: "delete(key: K): boolean;" },
    { name: "forEach", from: "Map",
      signature: "forEach(callbackfn: (value: V, key: K, map: Map<K, V>) => void, thisArg?: any): void;",
      drop: ["thisArg"] },
    // TypeScript's own `V | undefined`: a key the map lacks reads nothing.
    { name: "get", from: "Map", signature: "get(key: K): V | undefined;", effect: "preservesInputHeap" },
    { name: "has", from: "Map", signature: "has(key: K): boolean;", effect: "preservesInputHeap" },
    { name: "set", from: "Map", signature: "set(key: K, value: V): this;", resultIsReceiver: true },
    { name: "size", from: "Map", signature: "readonly size: number;" },
    { name: "[Symbol.toStringTag]", from: "Map", signature: "readonly [Symbol.toStringTag]: string;" },
    { name: "[Symbol.iterator]", from: "Map", signature: "[Symbol.iterator](): MapIterator<[K, V]>;",
      resultAs: "Iterator", effect: "preservesInputHeap" },
    { name: "keys", from: "Map", signature: "keys(): MapIterator<K>;", resultAs: "Iterator", effect: "preservesInputHeap" },
    { name: "values", from: "Map", signature: "values(): MapIterator<V>;", resultAs: "Iterator", effect: "preservesInputHeap" },
    { name: "entries", from: "Map", signature: "entries(): MapIterator<[K, V]>;", resultAs: "Iterator", effect: "preservesInputHeap" },
  ],
  Date: [
    ...["valueOf", "getTime", "getFullYear", "getUTCFullYear", "getMonth", "getUTCMonth", "getDate",
      "getUTCDate", "getDay", "getUTCDay", "getHours", "getUTCHours", "getMinutes", "getUTCMinutes",
      "getSeconds", "getUTCSeconds", "getMilliseconds", "getUTCMilliseconds", "getTimezoneOffset"]
      .map((name): OverlayEntry => ({ name, from: "Date", signature: `${name}(): number;`, effect: "preservesInputHeap" })),
    { name: "setTime", from: "Date", signature: "setTime(time: number): number;" },
    ...["toString", "toISOString"]
      .map((name): OverlayEntry => ({ name, from: "Date", signature: `${name}(): string;`, effect: "preservesInputHeap" })),
  ],
};

/** What the overlay reads through the declaration graph: the symbol a
 * computed key names, and a reference to a standard library interface, which
 * then joins the graph. */
export type OverlayLibrary = {
  symbol: (written: ts.PropertyAccessExpression | ts.Identifier) => number;
  /** Identity from the standard library, never a synthetic identifier node. */
  wellKnownSymbol: (name: string) => number | null;
  reference: (node: ts.InterfaceDeclaration, args: TypeTerm[], span: [number, number]) => TypeTerm;
};

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
   * `preservesInputHeap` where every listed member, at each signature the
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
    effect: "unrestricted",
    receiver: from => ({ k: "array", presence: "readable", readonly: from === "ReadonlyArray", element, span: [0, 0] }) });
  if (!entries.some(e => ["join", "toString", "sort"].includes(e.name))) return [result];
  const hook = library.wellKnownSymbol("toPrimitive");
  if (result.expression.k !== "object") throw Error("a prototype contract must be an object");
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
export function primitivePrototype(checker: Checker, at: Node, library: OverlayLibrary,
    kind: PrimitiveKind, entries: readonly OverlayEntry[] = primitiveOverlay[kind]): TypeDefinition {
  // A string's own keys are its `length` and its indices: never the prototype's.
  const owned = entries.find(e => kind === "string" && (e.name === "length" || /^\d/.test(e.name)));
  if (owned) throw Error(`a string owns '${owned.name}'; String.prototype's does not answer for it`);
  return prototype(checker, at, library, { identity: primitiveProtoIdentity(kind), binders: [], entries,
    effect: "preservesInputHeap", receiver: () => ({ k: "atom", name: kind, span: [0, 0] }) });
}

function prototype(checker: Checker, at: Node, library: OverlayLibrary, proto: Prototype): TypeDefinition {
  const declared = (name: string) => {
    const symbol = checker.resolveName(name, SymbolFlags.Interface, at, false);
    const parts = (symbol?.declarations ?? []).map(d => d.resolve())
      .filter((n): n is ts.InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
    if (!parts.length) throw Error(`the standard library declares no ${name}`);
    return parts;
  };
  const libraries = new Map<string, ts.InterfaceDeclaration[]>();
  const libraryOf = (name: string) => {
    const known = libraries.get(name);
    if (known) return known;
    const parts = declared(name);
    libraries.set(name, parts);
    return parts;
  };
  const interfaceOf = (name: "Iterator") => {
    const [first] = declared(name);
    if (!first) throw Error(`the standard library declares no ${name}`);
    return first;
  };
  const fields = proto.entries.flatMap(entry => {
    const named = libraryOf(entry.from).flatMap(part => part.members
      .filter(ts.isMethodSignatureDeclaration)
      .filter(m => (ts.isIdentifier(m.name) ? m.name.text : m.name.getText(part.getSourceFile())) === entry.name)
      .map(m => ({ member: m, source: part.getSourceFile() })));
    // A member the project's standard library does not declare, as `at`
    // before ES2022, is not part of its prototype.
    if (!named.length) return [];
    const found = named.filter(({ member, source }) =>
      member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length)
      throw Error(`${entry.from}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    const { member, source } = only;
    const span: [number, number] = [0, 0];
    const own = (member.typeParameters ?? []).map(p => p.name.text)
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
    const stated = entry.result ?? (entry.resultAs
      ? library.reference(interfaceOf(entry.resultAs), [{ k: "binder", name: "T", span }], span)
      : entry.resultIsReceiver ? receiver : undefined);
    const forms = entry.stated
      ? entry.stated.map(f => ({ k: "function", effect: f.effect ?? entry.effect ?? proto.effect, receiver: f.receiver ?? null,
          params: f.params, rest: null, result: f.result,
          span } satisfies Extract<TypeTerm, { k: "function" }>))
      : signatures(scope, parameters, entry.resultAs ? undefined : member.type, member, span, false, stated)
          .map(f => ({ ...f, effect: entry.effect ?? proto.effect }));
    const [first] = forms;
    if (!first || (!binders.length && forms.length !== 1))
      throw Error(`${entry.from}.${entry.name} requires a nonempty supported signature family`);
    const type: TypeTerm = binders.length
      ? { k: "scheme", binders: binders.map(name => ({ name, bound: entry.bounds?.[name] ?? null, resolution: null, default: null, span })),
          signatures: forms.map(f => ({ ...f, receiver: f.receiver ?? receiver })), span }
      : { ...first, receiver: first.receiver ?? receiver };
    const key = ts.isComputedPropertyName(member.name) &&
        (ts.isPropertyAccessExpression(member.name.expression) || ts.isIdentifier(member.name.expression))
      ? { symbol: library.symbol(member.name.expression) } : entry.name;
    return [{ name: key, optional: false, readonly: true, type, span }];
  });
  return { declaration: proto.identity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: [], span: [0, 0] } };
}
