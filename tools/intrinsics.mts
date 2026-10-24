/** `async`, `await`, `for...of`, argument spreads, array pattern slices and
 * `for...in` as trusted steps (SOURCE-CONTRACTS.md, "Async functions and
 * await", "Loops and spreads over iterables", "Patterns" and "Statement
 * forms"). Each is a
 * call of an intrinsic, a value no source name can denote: the parser writes
 * the async ones, and Lean compiles a `for...of` to its calls. The declaration
 * reader lists the intrinsics among the client's values at these signatures,
 * some over the standard library's `Promise`. Nothing checks them: like an
 * imported value's declared type, each is an assumption a result is relative
 * to.
 *
 * - `await e` is `%Await%(e)`: awaiting an awaitable value yields its
 *   observation (`X.Observed`): a stably non-thenable value itself, a native
 *   promise's fulfillment value, a value of its type argument, whatever that
 *   is. Other jobs may run in between, as they may during any call.
 * - `return e` in an async function is `return %AsyncReturn%(e)`: the promise
 *   the call returned settles to the fresh resolution of `e`
 *   (`X.Result`): `e` itself where it stays non-thenable, and what `e`
 *   settles to, resolved again, where it is a native promise. The lifetime
 *   `then` contract and the ordinary array invariant establish stability
 *   alongside primitives.
 * - Completing an async function is `return %AsyncComplete%()`: its promise
 *   settles to `undefined`, which `Promise<void>` admits.
 * - `for (const x of xs)` steps the iteration intrinsic the iterable's type
 *   picks (`iterationIntrinsic`): `%Iterate%(xs)` over an array, the array's
 *   iterator, which yields `{ value }` for each element in turn, reading the
 *   array's current length at each step, and then `null`. The others step
 *   the host's iterator of a string, a `Set`, a `Map` or a host collection
 *   iterator likewise. None of these iterators has a `return`, so a loop left
 *   early calls nothing.
 * - An argument spread `...x` of one of those others is `...%Spread:K%(x)`,
 *   the fresh array of what its iterator yields (`spreadName`).
 * - An array pattern's rest that is a slice, after `k` elements, is
 *   `%RestFrom:k%(xs)` (`restFromIntrinsic`).
 * - `for (const k in o)` is `for (const k of %ForIn%(o))`: the keys the loop
 *   visits, each a string, of any value (none for null or undefined).
 * - `for (const k in P) { const x = P[k]!; … }`, where the body reads the
 *   entry at the key before anything can change it and `P` still denotes the
 *   enumerated object there (`forInEntryReads` in the parser), steps
 *   `%Iterate:ForIn%(P)` instead, and the read is the step's value: over a
 *   dictionary, which
 *   holds no prototype, the keys the loop visits are its own, and each step
 *   yields a fresh `[key, value]` array, the value the one the dictionary
 *   holds under the key at the step. A plain object's prototype,
 *   `Object.prototype`, holds no enumerable key.
 * - `k in o` whose key TypeScript types as other than string literals is
 *   `%HasProperty%(k, o)`: whether `o`, an object, has the property the key
 *   converts to, its own or an inherited one, as the host answers it. The
 *   conversion of a string, a number or a symbol runs no code, and neither
 *   does the lookup on the objects a program holds (no proxy, DESIGN.md
 *   "Trust surface"); the answer is a Boolean, which narrows nothing.
 * - `xs[k]` of an array or a tuple at a key TypeScript types as `number` (no
 *   literal) is `%ElementAt%(xs, k)`: the property the number names, an
 *   element where it is an index below the length, an own property of
 *   another numeric key, which `Array<T>`'s declared `[n: number]: T` says
 *   holds a `T`, else `undefined`, since the built-in `Array.prototype` and
 *   `Object.prototype` own no numeric key. The read runs no code (no
 *   accessor or proxy, DESIGN.md "Trust surface").
 *
 * The reviewed overlay of library globals (`library-globals.mts`) reads some
 * members as these: `Promise.resolve(v)` is `%PromiseResolve%(v)`, which
 * retains a native promise through its constructor identity path or freshly
 * resolves a stably non-thenable value: a promise of `v`'s observation, what
 * awaiting `v` yields. `Promise.resolve()` is
 * `%AsyncComplete%()`, and
 * `Promise.all(ps)` is `%PromiseAll%(ps)`: a promise of the array of what
 * the promises settle to, in order, settling once each has. The array is
 * fresh and owns no `then`, so it is not adopted. `Promise.reject(r)` is
 * `%PromiseReject%(r)`, a promise rejected with `r`, whose await throws, and
 * `new Promise(executor)` is `%NewPromise%(executor)`: the executor is
 * called at once with the promise's resolving functions, and resolving
 * settles the promise to a primitive. `Symbol.for(k)` is `%SymbolFor%(k)`,
 * the registry's symbol for the string `k`, and `Symbol.keyFor(s)` is
 * `%SymbolKeyFor%(s)`, the string the registry holds `s` under, or
 * `undefined`: neither reads its receiver, and a string or a symbol argument
 * converts without running code. */
import { join } from "node:path";
import type { SourceTypeParameter, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { resolutionSlots } from "./type-term.mts";
import { emptyEffect, footprintEffect, ordinaryEffect } from "./type-graph.mts";

export const intrinsicModule = "tscert/intrinsics";
export const awaitName = "%Await%";
export const asyncReturnName = "%AsyncReturn%";
export const promiseResolveName = "%PromiseResolve%";
/** The file declaring `Resolvable`, the bound that makes a type parameter
 * resolution-qualified, recognized by this declaration's identity. Every
 * project a program writing it is checked in lists the file. */
export const resolvableDeclaration: string = join(import.meta.dirname, "resolvable.d.ts");
/** The intrinsics typed through a resolution descriptor, which need the
 * stable family `%Stable%` and the native `Promise`. */
export const resolutionIntrinsics: readonly string[] = ["%Await%", "%AsyncReturn%", "%PromiseResolve%"];
export const asyncCompleteName = "%AsyncComplete%";
export const iterateName = "%Iterate%";
const iteratePrefix = "%Iterate:";
const spreadPrefix = "%Spread:";
export const iterateStringName = "%Iterate:string%";
export const iterateSetName = "%Iterate:Set%";
export const iterateMapName = "%Iterate:Map%";
export const iterateIteratorName = "%Iterate:Iterator%";
export const iterateRegExpStringName = "%Iterate:RegExpString%";
export const forInName = "%ForIn%";
export const iterateForInName = "%Iterate:ForIn%";
export const hasPropertyName = "%HasProperty%";
export const elementAtName = "%ElementAt%";
export const promiseAllName = "%PromiseAll%";
export const promiseRejectName = "%PromiseReject%";
export const newPromiseName = "%NewPromise%";
export const symbolForName = "%SymbolFor%";
export const symbolKeyForName = "%SymbolKeyFor%";
/** `e instanceof Error`: whether `Error.prototype` is on `e`'s prototype
 * chain, a Boolean that states nothing of `e`. */
export const instanceOfErrorName = "%InstanceOf:Error%";
/** A failing `assert(v, m)` of `node:assert/strict`, lowered as `if (!v)
 * throw %AssertionFailure%(m)`: the fresh `AssertionError`. */
export const assertionFailureName = "%AssertionFailure%";
/** A checked access of an early binding that finds it uninitialized
 * (SOURCE-ELABORATION.md, "Lexical bindings before initialization"): allocates a
 * `ReferenceError` by the realm's intrinsic constructor, whatever a source
 * binding of that name holds, and throws it. */
export const throwUninitializedName = "%ThrowUninitialized%";

type Signature = Extract<TypeTerm, { k: "function" }>;
type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
const span: [number, number] = [0, 0];
const atom = (name: AtomName): Within<{ value: "any"; store: "grow" }, TypeTerm> => ({ k: "atom", name, span });
const binder: TypeTerm = { k: "binder", name: "T", span };
const either = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", span, parts });
const fn = (params: TypeTerm[], result: TypeTerm): Within<{ value: "any"; store: "grow" }, Signature> =>
  ({ k: "function", effect: ordinaryEffect, receiver: null, params, rest: null, result, span });
/** The values no object is: a promise resolved with one settles to it. */
const primitives: AtomName[] = ["null", "undefined", "boolean", "number", "string", "bigint", "symbol"];
const primitive: TypeTerm = { k: "union", span, parts: primitives.map(atom) };
/** The types no thenable inhabits: primitives, arrays (whose prototype holds
 * no `then`, and to which no step adds one), and objects whose `then` reads
 * a primitive or nothing. Fresh resolution preserves its literal payload
 * type at these types; resolving a thenable adopts its result. */
export const nonThenable: TypeTerm = { k: "union", span, parts: [...primitives.map(atom),
  { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "then", optional: true, readonly: true, type: primitive, span }] },
  { k: "array", presence: "readable", readonly: true, element: atom("unknown"), span }] };

/** `%Stable%`, the stable non-thenable family `N` resolution descriptors are
 * relative to: a stable input is its own observation and result
 * (SOURCE-CONTRACTS.md, "Implied bounds"). Listed as a type of the intrinsic
 * module wherever a descriptor is checked; Lean reads it by this identity. */
export const stableDefinition: TypeDefinition = {
  declaration: { module: "tscert/intrinsics", name: "%Stable%", span },
  parameters: [], bases: [], expression: nonThenable };

/** `() => { readonly value: E } | null`: an iterator step, `null` at the end. */
const stepOf = (element: TypeTerm): Signature => fn([], { k: "union", span, parts: [
  { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "value", optional: false, readonly: true, type: element, span }] },
  atom("null")] });
const step: Signature = stepOf(binder);

/** An iteration intrinsic beyond arrays, which a `for...of` steps where
 * TypeScript types its iterable as a string, a `Set`, a `Map`, or a host
 * collection iterator (`SetIterator`, `MapIterator`, which a `Set`'s or a
 * `Map`'s overlay members return as the marked native collection iterator,
 * `nativeCollection`, the parameter of `%Iterate:Iterator%`): each yields `{ value }` for what the host's iterator yields,
 * in turn, and then `null`, and none has a `return`.
 *
 * - A string's iterator yields its code points, each a string of one or two
 *   code units (the model's strings hold no lone surrogate, and the result
 *   is claimed only at `string`).
 * - A `Set`'s yields its elements in insertion order, one added during the
 *   loop included; a `Map`'s a fresh `[key, value]` array per entry.
 * - A collection iterator is its own iterator (`%IteratorPrototype%`'s
 *   `[Symbol.iterator]` returns it) and steps its collection.
 *
 * - A native regex's match iterator (`%Iterate:RegExpString%`), which
 *   `[Symbol.matchAll]` of a native regex returns, marked as such
 *   (`regexp.mts`): it steps a private clone of the regex with the standard
 *   `exec`, yielding each match. A structural iterator meets no marked type,
 *   so it is never stepped as this one.
 *
 * A spread form, `%Spread:K%` for `%Iterate:K%` (`spreadName`), takes the
 * same parameter and gives the fresh array of what the step yields.
 *
 * Each runs no client code. Creating a step allocates it: the empty
 * footprint. A step, and a spread, which steps to the end, write only the
 * iterator's own position and, for a match iterator, its clone's
 * `lastIndex`, each a number, and allocate what they yield:
 * `{value: any, store: keep}` (SOURCE-CONTRACTS.md, "Native footprints").
 * `library` gives a reference to a standard library interface at arguments,
 * `nativeMatches` the native match iterator of an element type.
 * Each is listed only for a file that iterates such a value. */
export function iterationIntrinsic(name: string, library: (name: "Set" | "Map" | "Iterator", args: TypeTerm[]) => TypeTerm,
    nativeMatches: (element: TypeTerm) => TypeTerm, nativeCollection: (element: TypeTerm) => TypeTerm):
    { name: string; typeParams: SourceTypeParameter<TypeTerm>[]; type: Signature } {
  const spread = name.startsWith(spreadPrefix);
  const kind = spread ? iteratePrefix + name.slice(spreadPrefix.length) : name;
  const key: TypeTerm = { k: "binder", name: "K", span };
  const value: TypeTerm = { k: "binder", name: "V", span };
  const t = [{ name: "T", bound: null, resolution: null }];
  const [typeParams, param, element]: [SourceTypeParameter<TypeTerm>[], TypeTerm, TypeTerm] =
    kind === iterateStringName ? [[], atom("string"), atom("string")]
    : kind === iterateSetName ? [t, library("Set", [binder]), binder]
    : kind === iterateMapName ? [[{ name: "K", bound: null, resolution: null }, { name: "V", bound: null, resolution: null }], library("Map", [key, value]),
      { k: "tuple", presence: "dense", readonly: false, required: [key, value], optional: [], rest: null, span }]
    : kind === iterateIteratorName ? [t, nativeCollection(binder), binder]
    : kind === iterateRegExpStringName ? [t, nativeMatches(binder), binder]
    : (() => { throw Error(`no iteration intrinsic ${name}`); })();
  // The step, or, for a spread, the fresh array of what the step yields until
  // it yields `null`, as `...` collects it.
  const changesValues = footprintEffect({ value: "any", store: "keep" });
  return { name, typeParams, type: spread
    ? { ...fn([param], { k: "array", presence: "dense", readonly: false, element, span }), effect: changesValues }
    : { ...fn([param], { ...stepOf(element), effect: changesValues }), effect: emptyEffect } };
}

/** The spread form of an iteration intrinsic: `...x` in an argument list, over
 * a value the step intrinsic `step` iterates, is `...%Spread:K%(x)`, a fresh
 * array of the elements the step yields, in order. */
export const spreadName = (step: string): string => spreadPrefix + step.slice(iteratePrefix.length);

/** The intrinsic an array pattern's rest after `k` elements steps where it is
 * a slice, a rest TypeScript types as no one tuple of required positions. */
const restFromName = (k: number): string => `%RestFrom:${k}%`;

/** `%RestFrom:k%<T>(xs: readonly [unknown?, …, unknown?, ...T[]]): T[]`, with
 * `k` optional positions: a fresh array of `xs`'s elements from `k` to its
 * current length. JavaScript steps the array's iterator on after the
 * pattern's `k` elements to the end, reading the length at each step; the
 * call, made after their reads and defaults, reads the current length as
 * that step does. The parameter states what the elements from `k` on are
 * whatever the first `k` hold, so a union of tuples of different lengths
 * meets it arm by arm: `[number] | [number, string]` at `T = string`. */
export function restFromIntrinsic(k: number):
    { name: string; typeParams: SourceTypeParameter<TypeTerm>[]; type: Signature } {
  return { name: restFromName(k), typeParams: [{ name: "T", bound: null, resolution: null }],
    type: fn([{ k: "tuple", presence: "readable", readonly: true, required: [], optional: Array.from({ length: k }, () => atom("unknown")),
      rest: binder, span }], { k: "array", presence: "readable", readonly: false, element: binder, span }) };
}

/** A number's spelling as a literal: its `Number::toString`, which reads back
 * as the same double, and `-0` for negative zero, which that spells `0`. */
export function numberText(value: number): Within<{ value: "any"; store: "grow" }, string> {
  return Object.is(value, -0) ? "-0" : String(value);
}

/** The literal type of an enum member's value. */
export function literalTerm(value: string | number, at: [number, number]): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return typeof value === "string"
    ? { k: "literal", name: "string", text: value, span: at }
    : { k: "literal", name: "number", text: numberText(value), span: at };
}

/** An enum's members: each one's name, and its value where TypeScript
 * computes one (`getConstantValue`), `undefined` where it is known only at
 * run time. */
export type EnumMemberValue = { name: string; value: string | number | undefined };

/** Whether an enum's object holds the reverse mapping at its numeric values'
 * keys (SOURCE-CONTRACTS.md, "Enums"): `stated` where TypeScript's emit
 * builds it or its runtime object is checked to hold it, `none` for the
 * environment's object, of which the members alone are assumed. */
export type EnumReverse = "stated" | "none";

/** The object type of an enum one of whose members' values is known only at
 * run time, or of an enum another module or the environment declares: each
 * member a readonly field at its value's literal type, or at `number` where
 * its value is known only at run time (TypeScript requires such a member to
 * be a number); with `reverse` stated, O^ρ(E), also each
 * numeric value TypeScript computes a readonly field at `string` under its
 * `ToString`, which holds the name of a member with that value. The keys are
 * in JavaScript's order where they are known: array index keys ascending,
 * then the others as the emit creates them. A reverse key of a value known
 * only at run time is no field. */
export function enumMembersTerm(members: readonly EnumMemberValue[], at: [number, number], reverse: EnumReverse): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const fields = new Map<string, Extract<TypeTerm, { k: "object" }>["fields"][number]>();
  const names = new Set(members.map(m => m.name));
  for (const m of members) {
    fields.set(m.name, { name: m.name, optional: false, readonly: true,
      type: m.value === undefined ? { k: "atom", name: "number", span: at } : literalTerm(m.value, at), span: at });
    if (reverse === "none" || typeof m.value !== "number") continue;
    const key = String(m.value);
    // No member is named by a canonical numeric string (TS2452; `NaN` and
    // `Infinity` are no finite value's key), so a reverse key replaces none.
    if (names.has(key)) throw Error(`an enum member named ${key} would be replaced by a reverse mapping`);
    if (!fields.has(key))
      fields.set(key, { name: key, optional: false, readonly: true, type: { k: "atom", name: "string", span: at }, span: at });
  }
  const index = (k: string) => /^(0|[1-9][0-9]*)$/.test(k) && Number(k) < 4294967295;
  const keyed = [...fields].map(([key, field]) => ({ key, field }));
  return { k: "object", span: at, stringIndex: null, calls: [], fields: [
    ...keyed.filter(f => index(f.key)).sort((a, b) => Number(a.key) - Number(b.key)).map(f => f.field),
    ...keyed.filter(f => !index(f.key)).map(f => f.field),
  ] };
}

/** The intrinsic building the object of the enum `name` one of whose
 * members' values is known only at run time. */
export const enumIntrinsicName = (name: string): string => `%Enum:${name}%`;

/** `%Enum:E%(o: O°): O^ρ`, with `O°` and `O^ρ` the enum's `enumMembersTerm`
 * without and with its reverse keys: given the fresh object of its members
 * at their values, it returns that object with the reverse mapping
 * TypeScript's emit adds, for each numeric member in turn the property its
 * value's `ToString` names, holding the member's name. Those keys are
 * canonical numeric strings, none a member's name (the parser refuses a
 * member named `NaN` or `Infinity`, and TypeScript any other numeric name),
 * so every member keeps its field, and each key of a value TypeScript
 * computes holds the name of the last member with that value, a string. */
export function enumIntrinsic(name: string, members: readonly EnumMemberValue[]):
    { name: string; typeParams: SourceTypeParameter<TypeTerm>[]; type: Signature } {
  return { name: enumIntrinsicName(name), typeParams: [],
    type: fn([enumMembersTerm(members, span, "none")], enumMembersTerm(members, span, "stated")) };
}

/** The intrinsics' binders and signatures, given the standard library's
 * `Promise` applied to an argument. */
export function intrinsics(promise: (argument: TypeTerm) => TypeTerm, needed: ReadonlySet<string>):
  { name: string; typeParams: SourceTypeParameter<TypeTerm>[]; type: Signature }[] {
  // `X : Resolvable`: a binder owning its observation and result;
  // `X : Awaitable`: a binder owning its observation.
  const resolvableSlots = resolutionSlots("X", "resolvable");
  const awaitableSlots = resolutionSlots("X", "awaitable");
  const resolvable: SourceTypeParameter<TypeTerm> = { name: "X", bound: null, resolution: resolvableSlots };
  const awaitable: SourceTypeParameter<TypeTerm> = { name: "X", bound: null, resolution: awaitableSlots };
  const input: TypeTerm = { k: "binder", name: "X", span };
  const observed: TypeTerm = { k: "binder", name: awaitableSlots.observation, span };
  const result: TypeTerm = { k: "binder", name: resolvableSlots.result, span };
  const definitions: Record<string, () => { typeParams: SourceTypeParameter<TypeTerm>[]; type: Signature }> = {
    // `await` yields the input's observation.
    [awaitName]: () => ({ typeParams: [awaitable], type: fn([input], observed) }),
    // Fresh resolution settles to the input's result.
    [asyncReturnName]: () => ({ typeParams: [resolvable], type: fn([input], promise(result)) }),
    // PromiseResolve returns a native input itself and wraps a stable one in
    // a fresh promise: a promise of the input's observation.
    [promiseResolveName]: () => ({ typeParams: [awaitable], type: fn([input], promise(observed)) }),
    [asyncCompleteName]: () => ({ typeParams: [], type: fn([], promise(atom("void"))) }),
    // The array's iterator, fresh: creating it changes nothing, and its
    // state is its own position, a number. Each step reads the array's
    // current length and an element, and writes only that position:
    // `{value: any, store: keep}` (SOURCE-CONTRACTS.md, "Native footprints").
    [iterateName]: () => ({ typeParams: [{ name: "T", bound: null, resolution: null }],
      type: { ...fn([{ k: "array", presence: "readable", readonly: true, element: binder, span }],
        { ...step, effect: footprintEffect({ value: "any", store: "keep" }) }), effect: emptyEffect } }),
    [promiseAllName]: () => ({ typeParams: [{ name: "T", bound: null, resolution: null }],
      type: fn([{ k: "array", presence: "readable", readonly: true, element: promise(binder), span }],
        promise({ k: "array", presence: "dense", readonly: false, element: binder, span })) }),
    // A promise rejected with the reason: awaiting it throws, so it is a
    // promise of every type, never settling to a value.
    [promiseRejectName]: () => ({ typeParams: [{ name: "T", bound: null, resolution: null }],
      type: fn([atom("unknown")], promise(binder)) }),
    // `new Promise(executor)`: the executor runs at once, given functions
    // that settle the promise to their argument, or reject it; a throw out
    // of the executor rejects it. This constructor contract admits primitive
    // payloads; resolving with a thenable would adopt it instead.
    [newPromiseName]: () => ({ typeParams: [{ name: "T", bound: primitive, resolution: null }],
      type: fn([fn([fn([binder], atom("void")), fn([atom("unknown")], atom("void"))], atom("void"))],
        promise(binder)) }),
    // The entries a `for...in` over a dictionary visits, each read at its
    // step: a fresh `[key, value]` array per key, then `null`.
    [iterateForInName]: () => ({ typeParams: [{ name: "V", bound: null, resolution: null }],
      type: fn([{ k: "object", span, fields: [], calls: [],
        stringIndex: { readonly: true, value: { k: "binder", name: "V", span }, span } }],
        stepOf({ k: "tuple", presence: "dense", readonly: false,
          required: [atom("string"), { k: "binder", name: "V", span }], optional: [], rest: null, span })) }),
    [forInName]: () => ({ typeParams: [],
      type: fn([atom("unknown")], { k: "array", presence: "readable", readonly: true, element: atom("string"), span }) }),
    // The lookup runs no code, no object being a proxy, and writes nothing.
    [hasPropertyName]: () => ({ typeParams: [],
      type: { ...fn([either(atom("string"), atom("number"), atom("symbol")), atom("object")], atom("boolean")),
        effect: emptyEffect } }),
    // It returns nothing and allocates the error it throws: within the
    // empty footprint over storage that existed before it, on its throw.
    [throwUninitializedName]: () => ({ typeParams: [],
      type: { ...fn([], atom("never")), effect: { ...emptyEffect, onThrow: true } } }),
    [symbolForName]: () => ({ typeParams: [], type: fn([atom("string")], atom("symbol")) }),
    // OrdinaryHasInstance walks the operand's prototype chain, which runs no
    // code, no object being a proxy, and writes nothing.
    // Building the error reads no argument but the message, a string, yet
    // runs a program's `Error.prepareStackTrace` and sets and restores
    // `Error.stackTraceLimit`: it states no effect.
    [assertionFailureName]: () => ({ typeParams: [],
      type: fn([either(atom("string"), atom("undefined"))], atom("unknown")) }),
    [instanceOfErrorName]: () => ({ typeParams: [],
      type: { ...fn([atom("unknown")], atom("boolean")), effect: emptyEffect } }),
    [symbolKeyForName]: () => ({ typeParams: [], type: fn([atom("symbol")], either(atom("string"), atom("undefined"))) }),
    // The read runs no code and writes nothing: an own numeric key of an
    // array holds a data property (`numericOwn`), and neither
    // `Array.prototype` nor `Object.prototype` owns one, so no getter runs.
    [elementAtName]: () => ({ typeParams: [{ name: "T", bound: null, resolution: null }],
      type: { ...fn([{ k: "array", presence: "readable", readonly: true, element: binder, span }, atom("number")],
        either(binder, atom("undefined"))), effect: emptyEffect } }),
  };
  return [...needed].map(name => {
    const make = definitions[name];
    if (!make) throw Error(`no intrinsic ${name}`);
    return { name, ...make() };
  });
}
