/** The standard library's global values, such as `BigInt` and `Symbol`, as a
 * client may use them: TypeScript's own declarations, as the project's
 * standard library states them, through a reviewed overlay (PROGRAM-TYPING.md,
 * "Library globals"). Nothing is vendored. As for `Array.prototype`
 * (`array-prototype.mts`), the overlay holds only what those declarations do
 * not say and soundness needs:
 *
 * - which signatures exist: a global's call, construct, method or property
 *   signature is read only when an entry lists it, with exactly the text it
 *   was reviewed against, so a changed library is refused and reviewed again;
 * - where the host runs code of the client's on an argument the declaration
 *   admits (`String` of an object calls its `toString`), the parameter the
 *   reader states instead: the part of the declared type on which it runs
 *   none (`admit`). Where the host only throws on an argument (`BigInt(1.5)`,
 *   a `RangeError`), the declaration is read as it is: a throw is an outcome,
 *   never a wrong value (DESIGN.md, "Throws");
 * - where the declaration states less than the host does (`any`) or more (a
 *   parameter at which it misbehaves), the signature the host meets, stated
 *   instead (`stated`);
 * - a member whose call is a primitive of the calculus: a test (`test`) or
 *   a trusted step already stated as an intrinsic (`intrinsic`);
 * - a call signature that holds of the global read as a value (`value`).
 *
 * A global declared outside the standard library, such as Node's `process`,
 * is read as its declaration states, member by member (`selectGlobal`). */
import { obligated, transparent, type HostClass } from "./host-operations.mts";
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { asyncCompleteName, promiseResolveName, newPromiseName, promiseAllName, promiseRejectName, symbolForName,
  symbolKeyForName } from "./intrinsics.mts";
import { emptyEffect } from "./type-graph.mts";
import type { CallEffect } from "./type-graph.mts";

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];

/** A signature the overlay states: its binders, its parameters, the element
 * type of its rest parameter where it has one, its result. */
export type Stated = { binders: string[]; params: TypeTerm[]; rest?: TypeTerm; result: TypeTerm };
/** A standard library interface applied to arguments, such as `Set<T>`. */
type LibraryReference = (name: string, args: TypeTerm[]) => TypeTerm;

export type GlobalEntry = {
  /** The global variable, `declare var BigInt: BigIntConstructor`. */
  global: string;
  /** The member read, `Symbol.for`; absent for a call of the global itself. */
  member?: string;
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** A parameter some declared arguments of which the host runs the client's
   * code on: it is stated as `safe`, the part on which it runs none. */
  admit?: { parameter: string; safe: AtomName[] };
  /** The call is a test of the calculus, not a call of the member: the
   * parser writes `Array.isArray(e)` as the test `isArray` of `e`, whose
   * narrowing Lean proves, and the member joins no value. An entry without a
   * member, whose signature is the variable's declaration, reads
   * `e instanceof X` as the test. */
  test?: "isArray";
  /** The call signature holds of the global read as a value: whoever
   * receives the value may call it with any receiver and any arguments the
   * signature admits, and the entry states what the host does at each. A
   * global is read as a value only where every call signature's entry says
   * so. */
  value?: true;
  /** The call runs the global's construct steps: the parser writes `Error(m)`
   * as `new Error(m)`, and the call is read at `stated` as a construct
   * signature, joining the global's construct signatures. */
  construct?: true;
  /** The call is a call of this intrinsic (`intrinsics.mts`), which states
   * the same step: the parser writes `Promise.resolve(v)` as
   * `%PromiseResolve%(v)`, and the member joins no value. */
  intrinsic?: string;
  /** The signature read instead of the declared one: its own binders, its
   * parameters, which a call may not exceed, and its result. What the host
   * does at these arguments, stated as a type. For a property, its type is
   * the result. */
  stated?: Stated | Stated[] | ((library: LibraryReference) => Stated | Stated[]);
  /** Declarations the stated signature names that no library declares, such
   * as `JsonValue`: they join the document when the entry is read. */
  definitions?: TypeDefinition[];
  /** The effect the read signature states, where reviewed: a call at the
   * parameters it states runs no client code and leaves every location it
   * did not allocate as it was. Absent, the signature states none. */
  effect?: CallEffect;
  /** The entry's classification against restricted values
   * (`host-operations.mts`). */
  host: HostClass;
};

const at: [number, number] = [0, 0];
const binder = (name: string): TypeTerm => ({ k: "binder", name, span: at });
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });
const optional = (type: TypeTerm): TypeTerm => ({ k: "union", parts: [type, atom("undefined")], span: at });
const readonlyArray = (element: TypeTerm): TypeTerm => ({ k: "array", presence: "readable", readonly: true, element, span: at });
const array = (element: TypeTerm): TypeTerm => ({ k: "array", presence: "readable", readonly: false, element, span: at });
/** The primitives, which ToNumber and ToString convert without running code. */
const primitive: TypeTerm = { k: "union", span: at,
  parts: [atom("null"), atom("undefined"), atom("boolean"), atom("number"), atom("string"), atom("bigint"),
    atom("symbol")] };
/** A descriptor `FromPropertyDescriptor` makes of an own property: a data
 * property's `value` and `writable` or an accessor's `get` and `set`, and
 * both kinds' `enumerable` and `configurable`. */
const descriptorField = (name: string, type: TypeTerm, isOptional: boolean) =>
  ({ name, optional: isOptional, readonly: true, type, span: at });
const propertyDescriptor: TypeTerm = { k: "object", stringIndex: null, calls: [], span: at, fields: [
  descriptorField("configurable", atom("boolean"), false), descriptorField("enumerable", atom("boolean"), false),
  descriptorField("value", atom("unknown"), true), descriptorField("writable", atom("boolean"), true),
  descriptorField("get", atom("unknown"), true), descriptorField("set", atom("unknown"), true)] };
const dictionary = (value: TypeTerm): TypeTerm =>
  ({ k: "object", fields: [], stringIndex: { readonly: true, value, span: at }, calls: [], span: at });

/** The values `JSON.stringify` serializes to a string with no code of the
 * client's run and no `undefined` returned: `null`, a Boolean, a number, a
 * string, or a dictionary of such values,
 *
 *     type JsonValue = null | boolean | number | string | { readonly [k: string]: JsonValue };
 *
 * A dictionary owns no `[[proto]]` and every string key it owns holds a
 * `JsonValue` (`dictViewT`), so no key it owns is callable and it inherits
 * only what `Object.prototype` holds: `toJSON` is never called, and no
 * getter runs. Arrays are left out: an array may own keys its type does not
 * state (DESIGN.md, "Arrays"), a callable `toJSON`
 * among them, which `stringify` would call, and whose result may be
 * `undefined`. A cycle throws, an outcome; a bigint would throw too, and is
 * left out as a value the host never serializes. */
const jsonValueIdentity: DeclarationIdentity = { module: "tscert/json", name: "JsonValue", span: at };
const jsonValue: TypeTerm = { k: "reference", args: [], span: at,
  reference: { name: jsonValueIdentity.name, span: at, arguments: [], target: jsonValueIdentity } };
const jsonValueDefinition: TypeDefinition = { declaration: jsonValueIdentity, parameters: [], bases: [],
  expression: { k: "union", span: at, parts: [atom("null"), atom("boolean"), atom("number"), atom("string"),
    dictionary(jsonValue)] } };



/** An entry whose parameters are primitives or whose contract states nothing
 * of an object argument's members. */
const contract = transparent("its contract holds of any value of its parameter types");

export const globalsOverlay: readonly GlobalEntry[] = [
  // Output, which the model does not observe. The host formats each argument
  // without running client code the fragment can write (no getters, no
  // symbol-keyed methods such as a custom inspection), and returns
  // `undefined`. `any` is read as `unknown`, so any argument is admitted.
  { host: obligated("each argument", "the host formats every reachable key of an object argument"), global: "console", member: "log", signature: "log(...data: any[]): void;" },
  // `BigInt(v)` throws a RangeError for a number that is not an integer and
  // a SyntaxError for a string that is not an integer's spelling; it runs no
  // code of the client's on a primitive, and returns a bigint otherwise.
  { host: contract, global: "BigInt", signature: "(value: bigint | boolean | number | string): bigint;" },
  // A new symbol whose description is the argument converted to a string,
  // which a string or number never fails.
  { host: contract, global: "Symbol", signature: "(description?: string | number): symbol;" },
  // The registry's members, which read no receiver: each call is a call of
  // the intrinsic stating its step, so `Symbol` called and read through them
  // is a callable value of its call signature alone.
  { host: contract, global: "Symbol", member: "for", signature: "for(key: string): symbol;", intrinsic: symbolForName },
  { host: contract, global: "Symbol", member: "keyFor", signature: "keyFor(sym: symbol): string | undefined;",
    intrinsic: symbolKeyForName },
  // The well-known symbols, each a symbol: stated at `symbol`, since the
  // reader has no `unique symbol` type of a library property. Which symbol
  // each is, a key the library's types use, is not read.
  ...["iterator", "asyncIterator", "hasInstance", "toPrimitive", "toStringTag"].map(
    (member): GlobalEntry => ({ host: contract, global: "Symbol", member, signature: `readonly ${member}: unique symbol;`,
      stated: { binders: [], params: [], result: atom("symbol") } })),
  // `String(v)` converts a primitive, a symbol included, without running
  // client code; an object's conversion calls its `toString` or `valueOf`,
  // which may throw or return an object, and then `String` throws.
  // At a primitive it writes nothing, so it states heap preservation.
  { host: contract, global: "String", signature: "(value?: any): string;", effect: emptyEffect,
    admit: { parameter: "value", safe: ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"] } },
  // `Number(v)` converts a primitive without running client code: a bigint
  // to the nearest number, a symbol throws a TypeError, an outcome. An
  // object's conversion calls its `Symbol.toPrimitive`, `valueOf` or
  // `toString`, client code, so the parameter is stated at the primitives,
  // where the call writes nothing and states heap preservation.
  { host: contract, global: "Number", signature: "(value?: any): number;", effect: emptyEffect,
    admit: { parameter: "value", safe: ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"] } },
  // `Boolean(v)` is ToBoolean of its first argument, which reads no property
  // and runs no code of any value's, and ignores every further argument;
  // `Boolean()` is `false`; it reads no receiver. So the global may be read
  // as a value (`xs.filter(Boolean)`), the callable
  // `(value: unknown, ...rest: unknown[]) => boolean`. The declaration
  // promises no narrowing, and none is stated: its result is a Boolean, which
  // a guard's promise is not. It writes nothing: heap preservation.
  { host: contract, global: "Boolean", signature: "<T>(value?: T): boolean;", value: true, effect: emptyEffect,
    stated: { binders: [], params: [atom("unknown")], rest: atom("unknown"), result: atom("boolean") } },
  // `Math.max(...vs)` and `Math.min(...vs)` convert every argument with
  // ToNumber before comparing: a primitive without running code (`undefined`
  // and a string that spells no number to `NaN`; a symbol and a bigint throw
  // a TypeError, an outcome), an object by its own `Symbol.toPrimitive`,
  // `valueOf` or `toString`, code of the client's. So each argument is
  // stated at the primitives, a hole a spread reads (`undefined`) included.
  // The result is a number: `NaN` if any argument converts to `NaN`, and
  // `-Infinity` (`max`) or `Infinity` (`min`) of no argument. At primitives
  // they run no code and write nothing: the empty footprint, as the
  // `String` conversions below.
  ...["max", "min"].map((member): GlobalEntry => ({ host: contract, global: "Math", member, effect: emptyEffect,
    signature: `${member}(...values: number[]): number;`,
    stated: { binders: [], params: [], rest: primitive, result: atom("number") } })),
  // `String.fromCodePoint(...cs)` converts every argument with ToNumber, as
  // `Math.max` does, and throws a RangeError where the number is no integer
  // from 0 to 0x10FFFF, an outcome; otherwise its result is a string.
  { host: contract, global: "String", member: "fromCodePoint", signature: "fromCodePoint(...codePoints: number[]): string;", effect: emptyEffect,
    stated: { binders: [], params: [], rest: primitive, result: atom("string") } },
  // `String.fromCharCode(...cs)` likewise, each number taken modulo 2^16 to a
  // code unit, which never throws.
  { host: contract, global: "String", member: "fromCharCode", signature: "fromCharCode(...codes: number[]): string;", effect: emptyEffect,
    stated: { binders: [], params: [], rest: primitive, result: atom("string") } },
  // Tests of a number that convert nothing: `false` for any argument that is
  // not a number, an object included, whose methods are never read. They
  // write nothing.
  { host: contract, global: "Number", member: "isFinite", signature: "isFinite(number: unknown): boolean;", effect: emptyEffect },
  { host: contract, global: "Number", member: "isInteger", signature: "isInteger(number: unknown): boolean;", effect: emptyEffect },
  { host: contract, global: "Number", member: "isSafeInteger", signature: "isSafeInteger(number: unknown): boolean;",
    effect: emptyEffect },
  // SameValue of the two arguments: identity of objects, equality of
  // primitives, no conversion and no client code, and no write. `any` is
  // read as `unknown`.
  { host: contract, global: "Object", member: "is", signature: "is(value1: any, value2: any): boolean;", effect: emptyEffect },
  // A fresh array of the object's own enumerable string keys: true of every
  // object, whatever its type says of its keys, and it runs no client code
  // (no getter is called). ES5 declares it at `object`, ES2015 at `{}`.
  { host: transparent("a fresh array of strings, which is all its contract states"), global: "Object", member: "keys", signature: "keys(o: object): string[];" },
  { host: transparent("a fresh array of strings, which is all its contract states"), global: "Object", member: "keys", signature: "keys(o: {}): string[];" },
  // The values of those keys, and the key-value pairs: nothing is known of
  // them, `any` read as `unknown`, and each pair is a fresh array. Reading a
  // value runs an accessor's getter: the fragment writes none, and a host
  // object's is assumed to return.
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "values", signature: "values(o: {}): any[];" },
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "entries", signature: "entries(o: {}): [string, any][];" },
  // `Object.getOwnPropertyDescriptor(o, k)`: ToObject of `o` (a TypeError of
  // `null` or `undefined`, an outcome; a primitive's wrapper otherwise), then
  // the key, which a string, number or symbol converts to without running
  // code, then `o`'s own lookup of it, [[GetOwnProperty]], which calls no
  // getter and runs no code on an ordinary or a built-in exotic object (a
  // proxy's would run its handler's trap: assumed of every object a program
  // holds, as `in` assumes it). The result is `undefined`, or a fresh
  // descriptor: `configurable` and `enumerable` Booleans, and `value` and
  // `writable`, or `get` and `set`. Nothing is known of `value`, a getter or
  // a setter: each is `unknown`, and the fields are stated readonly.
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "getOwnPropertyDescriptor",
    signature: "getOwnPropertyDescriptor(o: any, p: PropertyKey): PropertyDescriptor | undefined;",
    stated: { binders: [], params: [atom("unknown"),
      { k: "union", parts: [atom("string"), atom("number"), atom("symbol")], span: at }],
      result: optional(propertyDescriptor) } },
  // The generic overloads, which TypeScript selects for a record type whose
  // keys it does not bound, promise a `T` of every key's value. That is
  // true of a dictionary, whose every own string key holds a `T`
  // (`dictViewT`), and the parameter is stated at one: an open record may
  // own further keys of other types (`invalid-object-values-record.ts`),
  // and `ArrayLike<T>` is not read. Each pair is a fresh array.
  { host: transparent("the parameter is a dictionary, whose family admits no host object"), global: "Object", member: "values", signature: "values<T>(o: { [s: string]: T; } | ArrayLike<T>): T[];",
    stated: { binders: ["T"], params: [dictionary(binder("T"))], result: array(binder("T")) } },
  { host: transparent("the parameter is a dictionary, whose family admits no host object"), global: "Object", member: "entries",
    signature: "entries<T>(o: { [s: string]: T; } | ArrayLike<T>): [string, T][];",
    stated: { binders: ["T"], params: [dictionary(binder("T"))],
      result: array({ k: "tuple", presence: "dense", readonly: false, required: [atom("string"), binder("T")], optional: [],
        rest: null, span: at }) } },
  // A test of the array's identity, which the calculus makes itself
  // (`Tag.isArray`): true of exactly the objects that own an array store,
  // JavaScript's Array exotic objects. The declared guard, `arg is any[]`,
  // is not read: Lean narrows by the clauses of the tested value's type.
  { host: contract, global: "Array", member: "isArray", signature: "isArray(arg: any): arg is any[];", test: "isArray" },
  // `e instanceof Array`, entered by the variable's declaration: the same
  // test. `Array` owns no `[Symbol.hasInstance]`, and `Function.prototype`'s
  // cannot be replaced, so the operator walks `e`'s prototype chain for
  // `Array.prototype`. That finds it exactly for the arrays, under two
  // assumptions of the host: every array is made by the program's built-ins, and no
  // object inherits from `Array.prototype` but an array (the fragment makes
  // none: `class extends Array` and `Object.create` are refused, and it
  // cannot name `Array.prototype`).
  { host: contract, global: "Array", signature: "Array: ArrayConstructor", test: "isArray" },
  // `new Array()` and `new Array<T>()` are a fresh empty array, which is a
  // `T[]` at every `T`: the non-generic declaration's `any[]` states less
  // than that. An argument is refused: a single number is a length, and the
  // array it makes has holes, whose element contract would need a separate check.
  ...["new (arrayLength?: number): any[];", "new <T>(...items: T[]): T[];"].map(
    (signature): GlobalEntry => ({ host: contract, global: "Array", signature,
      stated: { binders: ["T"], params: [], result: { k: "array", presence: "readable", readonly: false, element: binder("T"), span: at } } })),
  // `new Error(m)` with a string owns `message`, that string, as a property
  // that is not enumerable: the model holds it on a prototype it gives the
  // object, so a read and `in` find it and a spread does not copy it. Its
  // `name` and a missing message are `Error.prototype`'s, which the model
  // does not hold, so only the message is stated, and it is required.
  // `stack` is the engine's and is not stated. ES2022 adds `options`.
  //
  // `Error(m)` called runs the same steps: with no new target, the error
  // constructor takes itself as the target (ECMA-262, "Error ( message [ ,
  // options ] )"), so the call is read as the construct, at the same
  // statement. It converts a string message with no code of the client's
  // and writes nothing it did not allocate: the empty footprint, on a throw
  // too.
  ...["new (message?: string): Error;", "new (message?: string, options?: ErrorOptions): Error;",
    "(message?: string): Error;", "(message?: string, options?: ErrorOptions): Error;"].map(
    (signature): GlobalEntry => ({ host: contract, global: "Error", signature,
      ...(signature.startsWith("new ") ? {} : { construct: true }), effect: { ...emptyEffect, onThrow: true },
      stated: { binders: [], params: [atom("string")],
        result: { k: "object", fields: [], stringIndex: null, calls: [], span: at,
          prototype: { k: "object", fields: [{ name: "message", optional: false, readonly: true,
            type: atom("string"), span: at }], stringIndex: null, calls: [], span: at } } } })),
  // PromiseResolve retains a native promise with the built-in standard
  // constructor, and freshly resolves stably non-thenable values. Without a
  // value, the promise settles to `undefined`, as an async completion does.
  { host: contract, global: "Promise", member: "resolve", signature: "resolve<T>(value: T): Promise<Awaited<T>>;",
    intrinsic: promiseResolveName },
  { host: contract, global: "Promise", member: "resolve", signature: "resolve(): Promise<void>;", intrinsic: asyncCompleteName },
  // `%PromiseAll%`: an array of promises, each settling to its type
  // argument as `%Await%` assumes, gives a promise of the array of their
  // values. The declaration's parameter, values of any kind each adopted, is
  // stated as an array of promises.
  { host: transparent("elements at Promise types: realm promises by the await assumption"), global: "Promise", member: "all",
    signature: "all<T extends readonly unknown[] | []>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]>; }>;",
    intrinsic: promiseAllName },
  // `new Set<T>(xs)` is a fresh set of the array's elements, `new Set<T>()`
  // an empty one, at every `T`. An array's iterator is the host's, which
  // runs no client code; any other iterable's is the client's, so the
  // parameter is stated at an array (`Set<T>`: `array-prototype.mts`). The
  // construction reads the array and allocates, so it states the empty
  // footprint; so does `new Map`'s. The iterable overload is stated at an
  // array and, separately, at a string, whose iterator is the host's too:
  // `new Set(s)` is a fresh set of the string's code points, a
  // `Set<string>`. One form at `readonly T[] | string` would be false at
  // `T := number`.
  { host: transparent("the array's store: a node list's table"), global: "Set", signature: "new <T = any>(values?: readonly T[] | null): Set<T>;", effect: emptyEffect,
    stated: library => ({ binders: ["T"], params: [optional(readonlyArray(binder("T")))],
      result: library("Set", [binder("T")]) }) },
  { host: transparent("the array's store: a node list's table"), global: "Set", signature: "new <T>(iterable?: Iterable<T> | null): Set<T>;", effect: emptyEffect,
    stated: library => [
      { binders: ["T"], params: [optional(readonlyArray(binder("T")))], result: library("Set", [binder("T")]) },
      { binders: ["T"], params: [atom("string")], result: library("Set", [atom("string")]) }] },
  // `new Map<K, V>(es)` is a fresh map of the array's pairs, each read at
  // its indices 0 and 1, and `new Map()` an empty one, at every `K` and `V`.
  ...["new (): Map<any, any>;", "new <K, V>(entries?: readonly (readonly [K, V])[] | null): Map<K, V>;",
    "new <K, V>(iterable?: Iterable<readonly [K, V]> | null): Map<K, V>;"]
    .map((signature): GlobalEntry => ({ host: transparent("an array of pairs, which no node list is"), global: "Map", signature, effect: emptyEffect,
      stated: library => ({ binders: ["K", "V"],
        params: [optional(readonlyArray({ k: "tuple", presence: "dense", readonly: true, required: [binder("K"), binder("V")],
          optional: [], rest: null, span: at }))],
        result: library("Map", [binder("K"), binder("V")]) }) })),
  // `new Date()` is now; `new Date(v)` converts a number or a string without
  // client code, but a `Date` argument, which any object meeting the
  // interface is, is converted by its own `valueOf` or `toString`: it is
  // stated at the primitives. With several numbers, each is a component.
  // An invalid date is a `Date` all the same, whose getters give `NaN`.
  { host: contract, global: "Date", signature: "new (): Date;" },
  ...["new (value: number | string): Date;", "new (value: number | string | Date): Date;"]
    .map((signature): GlobalEntry => ({ host: contract, global: "Date", signature,
      stated: library => ({ binders: [], params: [{ k: "union", parts: [atom("number"), atom("string")], span: at }],
        result: library("Date", []) }) })),
  { host: contract, global: "Date",
    signature: "new (year: number, monthIndex: number, date?: number, hours?: number, minutes?: number, seconds?: number, ms?: number): Date;" },
  // The current time, a number.
  { host: contract, global: "Date", member: "now", signature: "now(): number;" },
  // `JSON.parse(text)` is a fresh value built from the text, or a
  // SyntaxError: nothing is stated of it, `any` read as `unknown`. A
  // reviver is client code the host would call on every member, and whose
  // results replace them: the call is read with the text only.
  { host: contract, global: "JSON", member: "parse",
    signature: "parse(text: string, reviver?: (this: any, key: string, value: any) => any): any;",
    stated: { binders: [], params: [atom("string")], result: atom("unknown") } },
  // `JSON.stringify(v)` returns `undefined` for `undefined`, a symbol or a
  // function, calls a `toJSON` it finds, and throws on a bigint or a cycle;
  // at a `JsonValue` it does none of the first two and returns a string. A
  // replacer is client code: the call is read with the value only. At a
  // `JsonValue` it runs no code of the client's and writes nothing: it
  // reads own data properties and allocates the string, also before it
  // throws on a cycle, so the empty footprint holds on a throw too.
  { host: transparent("the parameter is JsonValue, whose string-key traversal reaches no host object"), global: "JSON", member: "stringify",
    signature: "stringify(value: any, replacer?: (this: any, key: string, value: any) => any, space?: string | number): string;",
    stated: { binders: [], params: [jsonValue], result: atom("string") }, definitions: [jsonValueDefinition],
    effect: { ...emptyEffect, onThrow: true } },
  // `%PromiseReject%`: a promise rejected with the reason, whose await
  // throws it, an outcome; it settles to no value, so it is a promise of
  // every type. The declared `any` is read as `unknown`: nothing runs on it.
  { host: contract, global: "Promise", member: "reject", signature: "reject<T = never>(reason?: any): Promise<T>;",
    intrinsic: promiseRejectName },
  // `%NewPromise%`: the executor is called at once with the promise's
  // resolving functions, and a throw out of it rejects the promise. The
  // declared `resolve` adopts a thenable (`T | PromiseLike<T>`); stated, it
  // takes a primitive, on which it settles.
  { host: contract, global: "Promise",
    signature: "new <T>(executor: (resolve: (value: T | PromiseLike<T>) => void, reject: (reason?: any) => void) => void): Promise<T>;",
    intrinsic: newPromiseName },
];

/** The entry for `global`'s `member` (absent: its call) declared as `text`. */
export function globalEntry(entries: readonly GlobalEntry[], global: string, member: string | undefined,
    text: string): GlobalEntry | undefined {
  return entries.find(e => e.global === global && e.member === member && e.signature === text);
}
