/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
import type { CallEffect, CallPromise, ClosedFootprint, ElementKind, ElementKinds, IndexFact, LinearTerm, PropertyKey } from "./declaration-types.mts";
import { requireWellFormed } from "./wire-strings.mts";
import {
  hasExactly,
  isJsonList,
  isJsonObject,
  type Json,
  type JsonObject,
  type JsonRead,
  type JsonValue,
} from "./calculus.mts";
export type { CallEffect, CallPromise, ClosedFootprint } from "./declaration-types.mts";
/** Physical density and a safe in-bounds read are distinct guarantees. */
export type ArrayPresence = "dense" | "readable" | "sparse";

/** The wire's order of strings, a string set's (HOST-FAMILIES.md, "Tag
 * sets"): lexicographic by Unicode code point, as Lean's `String` order and
 * OCaml's byte order of UTF-8 are. JavaScript's `<` compares UTF-16 code
 * units, which orders a code point past U+FFFF below one in U+E000–U+FFFF. */
export function codePointLess(a: string, b: string): boolean {
  const xs = [...a], ys = [...b];
  for (let i = 0; i < Math.min(xs.length, ys.length); i++) {
    const x = xs[i]?.codePointAt(0) ?? 0, y = ys[i]?.codePointAt(0) ?? 0;
    if (x !== y) return x < y;
  }
  return xs.length < ys.length;
}
export function isArrayPresence(value: unknown): value is Within<{ value: "keep"; store: "keep" }, ArrayPresence> {
  return value === "dense" || value === "readable" || value === "sparse";
}
export function presencePrefix(value: ArrayPresence): Within<{ value: "keep"; store: "keep" }, string> {
  return value === "readable" ? "" : `${value} `;
}
/** A union of labels. A table's labels are its row indices; the source
 * claims wire also writes label trees (`source-claims.mts`), so each row
 * type below is generic in its label. */
export type Labels<L = number> = L[];
/** A signature: the receiver a call may pass, then the parameters and the
 * result. A signature indifferent to its receiver names an unknown row. */
/** The footprint letting every location change: an ordinary arrow's. */
export const topFootprint: ClosedFootprint = { value: "any", store: "any" };
/** The footprint letting no location change: heap preservation. */
export const emptyFootprint: ClosedFootprint = { value: "keep", store: "keep" };
/** The six closed footprints, each after every one within it. */
export const closedFootprints: readonly ClosedFootprint[] = [
  { value: "keep", store: "keep" }, { value: "any", store: "keep" },
  { value: "keep", store: "grow" }, { value: "any", store: "grow" },
  { value: "keep", store: "any" }, { value: "any", store: "any" },
];
/** The optional guarantees a footprint's signature states. */
type EffectOptions = Partial<Omit<CallEffect, "footprint">>;
/** A fresh signature effect, with false and null for omitted guarantees. */
export const footprintEffect = (footprint: ClosedFootprint, options?: EffectOptions): Within<{ value: "keep"; store: "keep" }, CallEffect> =>
  ({ footprint, promise: options?.promise ?? null, fresh: options?.fresh ?? false,
    receiverStore: options?.receiverStore ?? false, onThrow: options?.onThrow ?? false,
    receiverOwn: options?.receiverOwn ?? false, freshObject: options?.freshObject ?? false,
    requires: options?.requires ?? null, elements: options?.elements ?? null, pre: options?.pre ?? [],
    ensures: options?.ensures ?? [] });
/** A fresh effect with a replacement promise and every other guarantee retained. */
export const withPromise = (effect: CallEffect, promise: CallPromise | null): Within<{ value: "keep"; store: "keep" }, CallEffect> =>
  ({ footprint: effect.footprint, promise, fresh: effect.fresh, receiverStore: effect.receiverStore,
    onThrow: effect.onThrow, receiverOwn: effect.receiverOwn, freshObject: effect.freshObject,
    requires: effect.requires, elements: effect.elements, pre: effect.pre, ensures: effect.ensures });
/** Heap preservation: no location may change, no promise. */
export const emptyEffect: CallEffect = footprintEffect(emptyFootprint);
/** An ordinary arrow's effect: every location may change, no promise. */
export const ordinaryEffect: CallEffect = footprintEffect(topFootprint);
/** A promise signature: a guard's or an assertion function's, about `param`,
 * whose code may change every location. */
export const promiseEffect = (asserts: boolean, param: number): Within<{ value: "keep"; store: "keep" }, CallEffect> =>
  footprintEffect(topFootprint, { promise: asserts ? { asserts: { param } } : { guards: { param } } });
export const sameFootprint = (a: ClosedFootprint, b: ClosedFootprint): boolean =>
  a.value === b.value && a.store === b.store;
const samePromise = (a: CallPromise | null, b: CallPromise | null): boolean =>
  a === null || b === null ? a === b
    : a.guards !== undefined ? b.guards !== undefined && a.guards.param === b.guards.param
    : b.asserts !== undefined && a.asserts.param === b.asserts.param;
export const sameEffect = (a: CallEffect, b: CallEffect): boolean =>
  sameFootprint(a.footprint, b.footprint) && samePromise(a.promise, b.promise) && a.fresh === b.fresh &&
    a.receiverStore === b.receiverStore && a.onThrow === b.onThrow && a.receiverOwn === b.receiverOwn &&
    a.freshObject === b.freshObject && sameKinds(a.requires, b.requires) && sameKinds(a.elements, b.elements) &&
    JSON.stringify(a.pre) === JSON.stringify(b.pre) && JSON.stringify(a.ensures) === JSON.stringify(b.ensures);
/** The kinds an elements predicate lists, each at most once, in this order. */
const elementKindOrder: readonly ElementKind[] =
  ["null", "undefined", "boolean", "number", "string", "bigint", "symbol", "object"];
const sameKinds = (a: ElementKinds | null, b: ElementKinds | null): boolean =>
  a === null || b === null ? a === b : a.length === b.length && a.every((k, i) => k === b[i]);
/** An elements predicate a value states: `null`, or kinds in their order,
 * each once; `undefined` where the value states neither. */
function decodeKinds(v: JsonRead): Within<{ value: "any"; store: "grow" }, ElementKinds | null | undefined> {
  if (v === null) return null;
  if (!Array.isArray(v)) return undefined;
  const kinds: ElementKind[] = [];
  let last = -1;
  for (const k of v) {
    const i = elementKindOrder.findIndex(o => o === k);
    if (i <= last) return undefined;
    last = i;
    const kind = elementKindOrder[i];
    if (kind === undefined) return undefined;
    kinds.push(kind);
  }
  return kinds;
}
/** A natural number a value states, or `undefined`. */
function decodeNat(v: JsonRead): number | undefined {
  return typeof v === "number" && Number.isSafeInteger(v) && v >= 0 ? v : undefined;
}
/** A safe integer a value states, or `undefined`. */
function decodeInt(v: JsonRead): number | undefined {
  return typeof v === "number" && Number.isSafeInteger(v) ? v : undefined;
}
/** The index facts a precondition or a result states (`CallEffect.pre`,
 * `CallEffect.ensures`), as fresh
 * objects, or `undefined` where the value is no list of them. */
export function decodeIndexFacts(v: JsonRead): Within<{ value: "any"; store: "grow" }, IndexFact[] | undefined> {
  if (!isJsonList(v)) return undefined;
  const facts: IndexFact[] = [];
  for (const f of v) {
    const fact = decodeIndexFact(f);
    if (fact === undefined) return undefined;
    facts.push(fact);
  }
  return facts;
}
/** A record's fields, where the value is a record of exactly these. */
function fieldsOf(v: JsonRead, names: readonly string[]): JsonObject | undefined {
  return isJsonObject(v) && Object.keys(v).sort().join(",") === [...names].sort().join(",") ? v : undefined;
}
function decodeIndexFact(v: JsonRead): IndexFact | undefined {
  if (!isJsonObject(v) || Object.keys(v).length !== 1) return undefined;
  const guarded = fieldsOf(v.guarded, ["slot", "path", "tag", "body"]);
  if (guarded) {
    const slot = decodeNat(guarded.slot);
    const path = guarded.path;
    const tag = guarded.tag;
    const body = decodeIndexFact(guarded.body);
    if (slot === undefined || body === undefined || (tag !== "null" && tag !== "undefined") || !isJsonList(path)) return undefined;
    const fields: string[] = [];
    for (const f of path) { if (typeof f !== "string") return undefined; fields.push(f); }
    return { guarded: { slot, path: fields, tag, body } };
  }
  const index = fieldsOf(v.index, ["slot"]);
  if (index) { const slot = decodeNat(index.slot); return slot === undefined ? undefined : { index: { slot } }; }
  const int = fieldsOf(v.int, ["slot"]);
  if (int) { const slot = decodeNat(int.slot); return slot === undefined ? undefined : { int: { slot } }; }
  const length = fieldsOf(v.length, ["array", "length"]);
  if (length) {
    const array = decodeNat(length.array);
    const len = decodeNat(length.length);
    return array === undefined || len === undefined ? undefined : { length: { array, length: len } };
  }
  const bound = fieldsOf(v.bound, ["array", "index", "strict"]);
  if (bound) {
    const array = decodeNat(bound.array);
    const index = decodeNat(bound.index);
    const strict = bound.strict;
    return array === undefined || index === undefined || typeof strict !== "boolean" ? undefined
      : { bound: { array, index, strict } };
  }
  const linear = fieldsOf(v.linear, ["fact"]);
  const fact = linear === undefined || !isJsonObject(linear.fact) || Object.keys(linear.fact).length !== 1 ? undefined
    : linear.fact;
  if (fact === undefined) return undefined;
  const le = fieldsOf(fact.le, ["form", "bound"]);
  const ne = fieldsOf(fact.ne, ["form", "bound"]);
  const body = le ?? ne;
  if (body === undefined || !isJsonList(body.form)) return undefined;
  const form: (readonly [LinearTerm, number])[] = [];
  for (const t of body.form) {
    if (!isJsonList(t) || t.length !== 2) return undefined;
    const x = decodeLinearTerm(t[0]);
    const c = decodeInt(t[1]);
    if (x === undefined || c === undefined) return undefined;
    form.push([x, c]);
  }
  const d = decodeInt(body.bound);
  if (d === undefined) return undefined;
  return { linear: { fact: le ? { le: { form, bound: d } } : { ne: { form, bound: d } } } };
}
/** A linear term (`HeapKnowledge.Term`): its kind, its root position and
 * the named data fields read from it. */
function decodeLinearTerm(v: JsonRead): LinearTerm | undefined {
  const t = fieldsOf(v, ["kind", "slot", "path"]);
  if (t === undefined) return undefined;
  const kind = t.kind;
  if (kind !== "value" && kind !== "length" && kind !== "view") return undefined;
  const slot = decodeNat(t.slot);
  if (slot === undefined || !isJsonList(t.path)) return undefined;
  const path: string[] = [];
  for (const f of t.path) {
    if (typeof f !== "string") return undefined;
    path.push(f);
  }
  return { kind, slot, path };
}
/** The closed footprint a value states, as a fresh object of its fields, or
 * `undefined` where the value states none. */
export function decodeClosedFootprint(v: JsonRead): Within<{ value: "any"; store: "grow" }, ClosedFootprint | undefined> {
  if (!isJsonObject(v) || Object.keys(v).length !== 2) return undefined;
  const value = v.value;
  const store = v.store;
  if (!isFootprintValue(value) || !isFootprintStore(store)) return undefined;
  return { value, store };
}
function isFootprintValue(v: unknown): v is ClosedFootprint["value"] {
  return v === "keep" || v === "any";
}
function isFootprintStore(v: unknown): v is ClosedFootprint["store"] {
  return v === "keep" || v === "grow" || v === "any";
}
/** The call effect a value states, as fresh objects of its fields, or
 * `undefined` where the value states none. */
export function decodeCallEffect(v: JsonRead): Within<{ value: "any"; store: "grow" }, CallEffect | undefined> {
  if (!isJsonObject(v) || Object.keys(v).length !== 11) return undefined;
  const requires = decodeKinds(v.requires);
  const elements = decodeKinds(v.elements);
  const pre = decodeIndexFacts(v.pre);
  const ensures = decodeIndexFacts(v.ensures);
  if (requires === undefined || elements === undefined || pre === undefined || ensures === undefined) return undefined;
  const footprint = decodeClosedFootprint(v.footprint);
  const fresh = v.fresh;
  const receiverStore = v.receiverStore;
  const onThrow = v.onThrow;
  const receiverOwn = v.receiverOwn;
  const freshObject = v.freshObject;
  if (footprint === undefined || typeof fresh !== "boolean" || typeof receiverStore !== "boolean" ||
      typeof onThrow !== "boolean" || typeof receiverOwn !== "boolean" ||
      typeof freshObject !== "boolean") return undefined;
  const stated = v.promise;
  let promise: CallPromise | null = null;
  if (stated !== null) {
    if (!isJsonObject(stated) || Object.keys(stated).length !== 1) return undefined;
    const guards = "guards" in stated;
    const about: JsonRead = guards ? stated.guards : "asserts" in stated ? stated.asserts : undefined;
    if (!isJsonObject(about) || Object.keys(about).length !== 1) return undefined;
    const param = about.param;
    if (typeof param !== "number" || !Number.isInteger(param) || param < 0) return undefined;
    promise = guards ? { guards: { param } } : { asserts: { param } };
  }
  return { footprint, promise, fresh, receiverStore, onThrow, receiverOwn, freshObject, requires, elements, pre,
    ensures };
}
/** One contract representation; every operand mapping must retain its effect. */
type CallContract<Receiver, Arguments, L = number> = {
  receiver: Receiver;
  arguments: Arguments;
  result: Labels<L>;
  effect: CallEffect;
};
type Arrow<L = number> = CallContract<Labels<L>, Labels<L>[], L>;
type MethodArrow<L = number> = CallContract<Record<string, never>, Labels<L>[], L>;
type MethodRestArrow<L = number> = CallContract<Record<string, never>, [Labels<L>[], Labels<L>], L>;
/** An object contract: one label list per named field, in the order the
 * producer wrote them. Fields a contract does not name are unconstrained. */
type Fields<L = number> = [name: PropertyKey, labels: Labels<L>][];
/** An optional field: constrains its key only where the object has it; a
 * readonly one is a view there. */
type OptionalField<L = number> = { key: PropertyKey; readonly: boolean; type: Labels<L> };
/** An own-key bound: the object's own keys are among `keys` (`among`), or
 * none of them is (an array owns no key its prototype provides). */
type KeyBound = { among: boolean; keys: PropertyKey[] };
/** A host-relative method member: its key, its fixed signatures
 * `[params, result]`, its variadic ones `[params, [rest, result]]`, and its
 * quantified ones, each a scheme row the member bound to its host meets, and
 * the types its host must meet for the fixed and variadic ones to hold. */
type MethodSig<L = number> = {
  key: PropertyKey;
  calls: MethodArrow<L>[];
  rests: MethodRestArrow<L>[];
  schemes: Labels<L>[];
  receivers: Labels<L>[];
};
type Tuple<L = number> = {
  required: Labels<L>[];
  optional: Labels<L>[];
  rest: Labels<L> | null;
  readonly: boolean;
  presence: ArrayPresence;
};
export type Clause<L = number> =
  | "nul"
  | "bool"
  | "undef"
  | "num"
  /** Semantic top: every value, and no operation through it. */
  | "top"
  | "source"
  | { boolLit: { value: boolean } }
  /** The double's bit pattern, decimal, as the consumer's UInt64. */
  | { numLit: { bits: string } }
  /** Strings, and one string, carried as itself. */
  | "str"
  | { strLit: { value: string } }
  /** Every bigint, and every symbol: an opaque value. */
  | "bigint"
  | "symbol"
  /** One bigint, as its integer: a JSON number of any length, which a
   * reader of this document shows and never computes with. */
  | { bigintLit: { value: number } }
  /** One symbol: the declaration document's `id`-th listed symbol, the one
   * a symbol key `{"symbol": id}` names. */
  | { symbolLit: { id: number } }
  /** A tag set (HOST-FAMILIES.md, "Tag sets"): two or more numbers by bit
   * pattern, or strings, sorted and distinct. */
  | { numIn: { bits: string[] } }
  | { strIn: { values: string[] } }
  /** `views` are read capabilities: a field read at a sound upper bound on
   * its contents, with no write permission through this contract. `optional`
   * fields constrain their key only where the object has it, as a view there
   * when readonly; `methods` are
   * host-relative members; each of `bounds` says which keys the object may
   * own; `stable` lists its stable keys (HOST-FAMILIES.md, "Stable keys").
   * Each is left out when there are none. */
  | { refs: { first: Fields<L>; rest: Fields<L>[]; views: Fields<L>; optional?: OptionalField<L>[];
      methods?: MethodSig<L>[]; bounds?: KeyBound[]; stable?: PropertyKey[] } }
  /** Readonly index views apply to every present own field their key class
   * admits; each of `cells`, a mutable index signature's, is also one every
   * such field holds exactly. Left out when there are none. */
  | {
      dict: {
        first: Fields<L>;
        rest: Fields<L>[];
        views: Fields<L>;
        indexes: IndexEntry<L>[];
        optional?: OptionalField<L>[];
        methods?: MethodSig<L>[];
        bounds?: KeyBound[];
        cells?: IndexEntry<L>[];
        stable?: PropertyKey[];
      };
    }
  /** A tuple contract on an array store: required positions, optional
   * positions, and the rest, or null when no further position may exist. */
  | { list: { first: Tuple<L>; rest: Tuple<L>[] } }
  /** An argument list under tuple contracts: what a rest parameter's type
   * says of the actuals past the fixed ones. */
  | { pack: { first: Tuple<L>; rest: Tuple<L>[] } }
  /** `variadic` signatures take actuals past their fixed parameters that, as
   * one argument list, are at the rest type, a `pack`; the field is left out
   * when there are none. */
  | { arrs: { arrows: Arrow<L>[]; variadic?: RestArrow<L>[] } }
  /** Construct signatures, each with its parameters, result and effect and
   * no receiver: what a class meets; and variadic ones, whose actuals past
   * the parameters are, as one argument list, at the rest type; the field is
   * left out when there are none. Its static fields, invariant record operands
   * as a callable's bag, `first` and `rest`, are left out when there are none. */
  | {
      ctors: {
        signatures: MethodArrow<L>[];
        variadic?: MethodRestArrow<L>[];
        first?: Fields<L>;
        rest?: Fields<L>[];
        views?: Fields<L>;
      };
    }
  | {
      callable: {
        first: Fields<L>;
        rest: Fields<L>[];
        arrows: Arrow<L>[];
        variadic?: RestArrow<L>[];
        methods?: MethodSig<L>[];
      };
    };
type RestArrow<L = number> = CallContract<Labels<L>, [Labels<L>[], Labels<L>], L>;
/** A producer's row: a union of clauses. */
export type Row<L = number> = Clause<L>[];
/** A verifier graph's row also may be a parameter, a binder a scheme
 * quantifies or a graph's assignment gives a family, a scheme, one
 * callable meeting its signatures at every instance of its binders, or a
 * meet, a value parameter within clauses (`V & DepSafe`)
 * (`POSITIVE-TYPES.md`, "Parameter and scheme rows"). */
type ParamRow = { kind: "value" | "arguments"; name: string; param: number };
export type SchemeRow<L = number> = { scheme: { binders: L[]; signatures: Arrow<L>[];
  bounds?: [binder: L, bound: Labels<L>][]; variadic?: RestArrow<L>[];
  resolution?: { input: number; observation: number; result: number | null }[];
  /** A construct scheme: its signatures are construct signatures. */
  construct?: true } };
/** `also`: the further value parameters the row meets beside `meet`. */
type MeetRow = { meet: number; clauses: Row; also?: number[] };
type GraphRow = Row | ParamRow | SchemeRow | MeetRow;
export type TypeGraph = GraphRow[];

/** The clause kinds, split so that every consumer can be made to cover them. */
export type StringClause = Extract<Clause, string>;
/** The object clauses' keys, each once. */
const CLAUSE_KEYS = [
  "boolLit", "numLit", "strLit", "numIn", "strIn", "bigintLit", "symbolLit",
  "refs", "dict", "ctors", "list", "pack", "arrs", "callable",
] as const;
export type ClauseKey = (typeof CLAUSE_KEYS)[number];
/** `ClauseKey` is exactly the keys of `Clause`'s object members: a key missing
 * from `CLAUSE_KEYS`, or one no member has, does not compile. `keyof` over a
 * union intersects, so the key extraction distributes. */
type KeysOf<T> = T extends unknown ? keyof T : never;
type Covers<Missing extends never> = Missing;
type EveryClauseKey = Covers<Exclude<KeysOf<Exclude<Clause, string>>, ClauseKey>>;
type OnlyClauseKeys = Covers<Exclude<ClauseKey, KeysOf<Exclude<Clause, string>>>>;

/** The string clauses, each once: a clause of `Clause` missing here, or a
 * string no clause is, does not compile. With `CLAUSE_KEYS`, these are the
 * only places a clause kind is enumerated. */
const STRING_CLAUSE_KEYS = [
  "nul", "bool", "undef", "num", "str", "top", "source", "bigint", "symbol",
] as const;
type EveryStringClause = Covers<Exclude<StringClause, (typeof STRING_CLAUSE_KEYS)[number]>>;
type OnlyStringClauses = Covers<Exclude<(typeof STRING_CLAUSE_KEYS)[number], StringClause>>;

/** The number a literal's bit pattern denotes. Readers show the number; the
 * bits are its identity, not its display. */
export const numberOfBits = (bits: string): Within<{ value: "keep"; store: "keep" }, number> => {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  return view.getFloat64(0);
};


function obj(v: JsonRead, keys: string[]): JsonObject {
  return objOptional(v, keys, []);
}
function objOptional(
  v: JsonRead,
  keys: string[],
  optional: string[],
): JsonObject {
  if (!isJsonObject(v) || !hasExactly(v, keys, optional))
    throw Error("unexpected type graph fields");
  return v;
}
function array(v: JsonRead): readonly JsonValue[] {
  if (!isJsonList(v)) throw Error("expected graph list");
  return v;
}
/** Each element of a list, decoded in order, as a fresh dense list. */
function each<T>(v: JsonRead, decode: (x: JsonValue) => T): T[] {
  const result: T[] = [];
  for (const x of array(v)) result.push(decode(x));
  return result;
}
/** A reference to one of `size` rows. */
function labelAt(i: JsonRead, size: number): number {
  if (typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= size)
    throw Error("type graph reference out of bounds");
  return i;
}
/** A union of references to `size` rows, as a fresh list. */
export function decodeLabels(v: JsonRead, size: number): Labels {
  return array(v).map((i) => labelAt(i, size));
}
/** The keys an index signature constrains: every string key, the canonical
 * numeric ones, or every symbol key (Lean's `IndexKeys`). */
type IndexClass = "strings" | "numeric" | "symbols";
/** An index contract: its key class and the type of each present key. */
type IndexEntry<L = number> = [IndexClass, Labels<L>];
function isIndexClass(v: unknown): v is IndexClass {
  return v === "strings" || v === "numeric" || v === "symbols";
}
function isParamKind(v: unknown): v is ParamRow["kind"] {
  return v === "value" || v === "arguments";
}
/** A key as TypeScript writes it: a string plainly, a symbol by its index. */
const keyText = (name: PropertyKey): string =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;
/** The decoders of a row, and of its clauses, whose labels `label` and
 * `labels` read: the graph's row references, or the claims document's
 * labels. */
type ClauseDecoders<L> = {
  clauses: (row: JsonRead) => Row<L>;
  row: (row: JsonRead) => Row<L> | SchemeRow<L>;
};
function clauseDecoders<L>(label: (v: JsonRead) => L, labels: (v: JsonRead) => Labels<L>): ClauseDecoders<L> {
  const labelLists = (v: JsonRead): Labels<L>[] => each(v, labels);
  const indexEntry = (v: JsonRead): IndexEntry<L> => {
    const pair = array(v);
    const keyClass = pair[0];
    if (pair.length !== 2 || !isIndexClass(keyClass))
      throw Error("expected an index key class and its type");
    return [keyClass, labels(pair[1])];
  };
  const signature = (v: JsonRead): JsonObject =>
    obj(v, ["receiver", "arguments", "result", "effect"]);
  const effect = (sig: JsonObject): CallEffect => {
    const decoded = decodeCallEffect(sig.effect);
    if (decoded === undefined) throw Error("invalid callable effect");
    return decoded;
  };
  const restArguments = (v: JsonRead): [Labels<L>[], Labels<L>] => {
    const args = array(v);
    if (args.length !== 2) throw Error("expected fixed arguments and a rest contract");
    const fixed = labelLists(args[0]);
    return [fixed, labels(args[1])];
  };
  const arrow = (v: JsonRead): Arrow<L> => {
    const sig = signature(v);
    const receiver = labels(sig.receiver);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver, arguments: labelLists(sig.arguments), result, effect: e };
  };
  const restArrow = (v: JsonRead): RestArrow<L> => {
    const sig = signature(v);
    const receiver = labels(sig.receiver);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver, arguments: restArguments(sig.arguments), result, effect: e };
  };
  const methodArrow = (v: JsonRead): MethodArrow<L> => {
    const sig = signature(v);
    obj(sig.receiver, []);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver: {}, arguments: labelLists(sig.arguments), result, effect: e };
  };
  const methodRestArrow = (v: JsonRead): MethodRestArrow<L> => {
    const sig = signature(v);
    obj(sig.receiver, []);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver: {}, arguments: restArguments(sig.arguments), result, effect: e };
  };
  const arrows = (v: JsonRead): Arrow<L>[] => each(v, arrow);
  // Left out when empty: an explicit empty list is not the canonical form.
  const variadic = (v: JsonRead): RestArrow<L>[] => {
    const sigs = array(v);
    if (!sigs.length) throw Error("an empty variadic list is written by omitting it");
    return each(sigs, restArrow);
  };
  const methodVariadic = (v: JsonRead): MethodRestArrow<L>[] => {
    const sigs = array(v);
    if (!sigs.length) throw Error("an empty variadic list is written by omitting it");
    return each(sigs, methodRestArrow);
  };
  // A key: a string, or `{"symbol": i}` for the declaration document's i-th
  // symbol.
  const key = (v: JsonRead, what: string): PropertyKey => {
    if (typeof v === "string") return v;
    const r = obj(v, ["symbol"]);
    if (typeof r.symbol !== "number" || !Number.isSafeInteger(r.symbol) || r.symbol < 0)
      throw Error(`expected ${what}`);
    return { symbol: r.symbol };
  };
  const fields = (v: JsonRead, repeated = false): Fields<L> => {
    const names = new Set<string>();
    const result: Fields<L> = [];
    for (const f of array(v)) {
      const pair = array(f);
      if (pair.length !== 2)
        throw Error("expected a field name and its labels");
      const k = key(pair[0], "a field name");
      const name = keyText(k);
      if (!repeated && names.has(name))
        throw Error("duplicate field in an object contract");
      names.add(name);
      const field: [PropertyKey, Labels<L>] = [k, labels(pair[1])];
      result.push(field);
    }
    return result;
  };
  const fieldLists = (v: JsonRead): Fields<L>[] => each(v, (f) => fields(f));
  const optionalFields = (v: JsonRead): OptionalField<L>[] => {
    const names = new Set<string>();
    const result: OptionalField<L>[] = [];
    for (const f of array(v)) {
      const r = obj(f, ["key", "readonly", "type"]);
      const k = key(r.key, "an optional field's key");
      const name = keyText(k);
      if (names.has(name)) throw Error("duplicate optional field in an object contract");
      names.add(name);
      const readonly = r.readonly;
      if (typeof readonly !== "boolean") throw Error("expected an optional field's readonly flag");
      result.push({ key: k, readonly, type: labels(r.type) });
    }
    return result;
  };
  const methods = (v: JsonRead): MethodSig<L>[] =>
    each(v, (m) => {
      const r = obj(m, ["key", "calls", "rests", "schemes", "receivers"]);
      const k = key(r.key, "a method key");
      const schemes = labelLists(r.schemes);
      const receivers = labelLists(r.receivers);
      const calls = each(r.calls, methodArrow);
      const rests = each(r.rests, methodRestArrow);
      return { key: k, calls, rests, schemes, receivers };
    });
  const bounds = (v: JsonRead): KeyBound[] =>
    each(v, (b) => {
      const r = obj(b, ["among", "keys"]);
      const among = r.among;
      if (typeof among !== "boolean") throw Error("invalid key bound");
      return { among, keys: each(r.keys, (k) => key(k, "a key in a bound")) };
    });
  // A record's stable keys (HOST-FAMILIES.md, "Stable keys"): a nonempty
  // list of keys, omitted when empty.
  const stableKeys = (v: JsonRead): PropertyKey[] => {
    const ks = array(v);
    if (!ks.length) throw Error("an empty stable-key list is written by omitting it");
    return each(ks, (k) => key(k, "a stable key"));
  };
  const tuple = (v: JsonRead): Tuple<L> => {
    const t = obj(v, ["required", "optional", "rest", "readonly", "presence"]);
    const presence = t.presence;
    if (!isArrayPresence(presence)) throw Error("invalid tuple density flag");
    const readonly = t.readonly;
    if (typeof readonly !== "boolean")
      throw Error("invalid tuple readonly flag");
    const required = labelLists(t.required);
    const optional = labelLists(t.optional);
    const rest = t.rest === null ? null : labels(t.rest);
    return { required, optional, rest, readonly, presence };
  };
  const tuples = (v: JsonRead): { first: Tuple<L>; rest: Tuple<L>[] } => {
    const r = obj(v, ["first", "rest"]);
    const first = tuple(r.first);
    return { first, rest: each(r.rest, tuple) };
  };
  // One decoder per clause kind. A missing key does not compile, so a new
  // clause cannot reach the decoder as a silent "unknown graph clause".
  // Keyed by the language's own union, so a clause added there and not here is
  // a type error; read only at the key of `CLAUSE_KEYS` equal to the
  // document's, so a clause this does not know, `toString` among them, is a
  // refusal rather than a silent pass.
  const decode: Record<ClauseKey, (body: JsonRead) => Clause<L>> = {
    boolLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "boolean")
        throw Error("invalid Boolean literal");
      return { boolLit: { value } };
    },
    // The identity is the double's bit pattern, decimal, as an unsigned 64.
    numLit: (b) => {
      const bits = obj(b, ["bits"]).bits;
      if (
        typeof bits !== "string" ||
        !/^[0-9]+$/.test(bits) ||
        BigInt(bits) > 0xffffffffffffffffn
      )
        throw Error("invalid numeric literal");
      return { numLit: { bits } };
    },
    strLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "string")
        throw Error("invalid string literal");
      return { strLit: { value } };
    },
    // Sorted and distinct, at least two: the one spelling of a set.
    numIn: (b) => {
      const bits = array(obj(b, ["bits"]).bits).map((x) => {
        if (typeof x !== "string" || !/^[0-9]+$/.test(x) || BigInt(x) > 0xffffffffffffffffn)
          throw Error("invalid number set");
        return x;
      });
      const numbers = bits.map((x) => BigInt(x));
      if (numbers.length < 2 || numbers.some((x, i) => i > 0 && !((numbers[i - 1] ?? x) < x)))
        throw Error("invalid number set");
      return { numIn: { bits } };
    },
    strIn: (b) => {
      const values = array(obj(b, ["values"]).values).map((x) => {
        if (typeof x !== "string") throw Error("invalid string set");
        return x;
      });
      if (values.length < 2 || values.some((x, i) => i > 0 && !codePointLess(values[i - 1] ?? x, x)))
        throw Error("invalid string set");
      return { strIn: { values } };
    },
    bigintLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "number" || !Number.isInteger(value))
        throw Error("invalid bigint literal");
      return { bigintLit: { value } };
    },
    symbolLit: (b) => {
      const id = obj(b, ["id"]).id;
      if (typeof id !== "number" || !Number.isSafeInteger(id) || id < 0)
        throw Error("invalid symbol identity");
      return { symbolLit: { id } };
    },
    refs: (b) => {
      const r = objOptional(b, ["first", "rest", "views"], ["optional", "methods", "bounds", "stable"]);
      // A verifier graph's record is a meet of field constraints: the
      // intersection of two records constraining one key states the key once
      // per constraint, as the views below do.
      const first = fields(r.first, true);
      const rest = fieldLists(r.rest);
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      const views = fields(r.views, true);
      const optional = "optional" in r ? optionalFields(r.optional) : undefined;
      const sigs = "methods" in r ? methods(r.methods) : undefined;
      const keyBounds = "bounds" in r ? bounds(r.bounds) : undefined;
      const stable = "stable" in r ? stableKeys(r.stable) : undefined;
      return {
        refs: {
          first, rest, views,
          ...(optional === undefined ? {} : { optional }),
          ...(sigs === undefined ? {} : { methods: sigs }),
          ...(keyBounds === undefined ? {} : { bounds: keyBounds }),
          ...(stable === undefined ? {} : { stable }),
        },
      };
    },
    dict: (b) => {
      const r = objOptional(b, ["first", "rest", "views", "indexes"], ["optional", "methods", "bounds", "cells", "stable"]);
      const first = fields(r.first);
      const rest = fieldLists(r.rest);
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      const views = fields(r.views, true);
      const indexes = each(r.indexes, indexEntry);
      const cells = "cells" in r ? each(r.cells, indexEntry) : undefined;
      const optional = "optional" in r ? optionalFields(r.optional) : undefined;
      const sigs = "methods" in r ? methods(r.methods) : undefined;
      const keyBounds = "bounds" in r ? bounds(r.bounds) : undefined;
      const stable = "stable" in r ? stableKeys(r.stable) : undefined;
      return {
        dict: {
          first, rest, views, indexes,
          ...(optional === undefined ? {} : { optional }),
          ...(sigs === undefined ? {} : { methods: sigs }),
          ...(keyBounds === undefined ? {} : { bounds: keyBounds }),
          ...(cells === undefined ? {} : { cells }),
          ...(stable === undefined ? {} : { stable }),
        },
      };
    },
    ctors: (b) => {
      const r = objOptional(b, ["signatures"], ["variadic", "first", "rest", "views"]);
      const first = "first" in r ? fields(r.first) : undefined;
      const rest = "rest" in r ? fieldLists(r.rest) : undefined;
      const views = "views" in r ? fields(r.views, true) : undefined;
      const signatures = each(r.signatures, methodArrow);
      const sigs = "variadic" in r ? methodVariadic(r.variadic) : undefined;
      return {
        ctors: {
          signatures,
          ...(sigs === undefined ? {} : { variadic: sigs }),
          ...(first === undefined ? {} : { first }),
          ...(rest === undefined ? {} : { rest }),
          ...(views === undefined ? {} : { views }),
        },
      };
    },
    list: (b) => ({ list: tuples(b) }),
    pack: (b) => ({ pack: tuples(b) }),
    arrs: (b) => {
      const r = objOptional(b, ["arrows"], ["variadic"]);
      const fixed = arrows(r.arrows);
      const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
      return { arrs: { arrows: fixed, ...(sigs === undefined ? {} : { variadic: sigs }) } };
    },
    callable: (b) => {
      const r = objOptional(b, ["first", "rest", "arrows"], ["variadic", "methods"]);
      const first = fields(r.first);
      const rest = fieldLists(r.rest);
      const fixed = arrows(r.arrows);
      const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
      const members = "methods" in r ? methods(r.methods) : undefined;
      return {
        callable: {
          first, rest, arrows: fixed,
          ...(sigs === undefined ? {} : { variadic: sigs }),
          ...(members === undefined ? {} : { methods: members }),
        },
      };
    },
  };

  const clauses = (row: JsonRead): Row<L> => {
    const result: Row<L> = [];
    for (const c of array(row)) {
      if (typeof c === "string") {
        const kind = STRING_CLAUSE_KEYS.find((k) => k === c);
        if (kind === undefined) throw Error("unknown graph clause");
        result.push(kind);
        continue;
      }
      if (!isJsonObject(c)) throw Error("unknown graph clause");
      // The clause's one key and its body, read from its own entries.
      const entries = Object.entries(c);
      const entry = entries[0];
      const kind = entry === undefined ? undefined : CLAUSE_KEYS.find((k) => k === entry[0]);
      if (entry === undefined || kind === undefined) throw Error("unknown graph clause");
      if (entries.length !== 1) throw Error("unexpected type graph fields");
      const decodeClause = decode[kind];
      result.push(decodeClause(entry[1]));
    }
    return result;
  };
  // A row: a scheme, or a union of clauses.
  const row = (v: JsonRead): Row<L> | SchemeRow<L> =>
    isJsonObject(v) && "scheme" in v ? scheme(obj(v, ["scheme"]).scheme) : clauses(v);
  const scheme = (v: JsonRead): SchemeRow<L> => {
    const r = objOptional(v, ["binders", "signatures"],
      ["bounds", "variadic", "resolution", "construct"]);
    if ("construct" in r && r.construct !== true) throw Error("a scheme's construct field, when present, is true");
    const binders = each(r.binders, label);
    const signatures = arrows(r.signatures);
    const binderBounds = "bounds" in r
      ? each(r.bounds, (b): [L, Labels<L>] => {
          const pair = array(b);
          if (pair.length !== 2) throw Error("expected a binder and its bound");
          const binder = label(pair[0]);
          return [binder, labels(pair[1])];
        })
      : undefined;
    const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
    let resolution: { input: number; observation: number; result: number | null }[] | undefined;
    if ("resolution" in r) {
      const owned = new Set<number>();
      const slot = (s: JsonRead): number => {
        if (typeof s !== "number" || !Number.isSafeInteger(s) || s < 0 ||
            s >= binders.length || owned.has(s))
          throw Error("resolution slots must be distinct binder positions");
        owned.add(s);
        return s;
      };
      const groups: { input: number; observation: number; result: number | null }[] = [];
      for (const group of array(r.resolution)) {
        const slots = obj(group, ["input", "observation", "result"]);
        // An awaitable group has no result slot.
        const input = slot(slots.input);
        const observation = slot(slots.observation);
        const result = slots.result === null ? null : slot(slots.result);
        groups.push({ input, observation, result });
      }
      resolution = groups;
    }
    const construct = "construct" in r;
    return {
      scheme: {
        binders, signatures,
        ...(binderBounds === undefined ? {} : { bounds: binderBounds }),
        ...(sigs === undefined ? {} : { variadic: sigs }),
        ...(resolution === undefined ? {} : { resolution }),
        ...(construct ? { construct: true as const } : {}),
      },
    };
  };
  return { clauses, row };
}
/** The rows of a claims document's table, each a scheme or a union of
 * clauses whose labels `label` reads, as fresh rows. */
export function decodeRows<L>(v: JsonRead, label: (v: JsonRead) => L): (Row<L> | SchemeRow<L>)[] {
  return each(v, clauseDecoders(label, (x) => each(x, label)).row);
}
/** The type graph a parsed document states, as fresh rows of the clauses it
 * checked. */
export function decodeGraph(value: Json | undefined): TypeGraph {
  requireWellFormed(value, "type graph");
  const rows = array(value);
  const label = (v: JsonRead): number => labelAt(v, rows.length);
  const labels = (v: JsonRead): Labels => decodeLabels(v, rows.length);
  const { clauses, row: schemeOrClauses } = clauseDecoders(label, labels);
  const graph: TypeGraph = [];
  rows.forEach((row, index) => {
    if (isJsonObject(row) && "meet" in row) {
      const r = objOptional(row, ["clauses", "meet"], ["also"]);
      const meet = label(r.meet);
      const also = "also" in r ? each(r.also, label) : undefined;
      graph.push({ meet, clauses: clauses(r.clauses), ...(also === undefined ? {} : { also }) });
      return;
    }
    if (isJsonObject(row) && "param" in row) {
      const r = obj(row, ["kind", "name", "param"]);
      const kind = r.kind, name = r.name;
      if (!isParamKind(kind) || typeof name !== "string" ||
          r.param !== index)
        throw Error("invalid parameter row");
      graph.push({ kind, name, param: index });
      return;
    }
    graph.push(schemeOrClauses(row));
  });
  return graph;
}
