/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
import type { CallEffect, CallPromise, ClosedFootprint, PropertyKey } from "./declaration-types.mts";
import { requireWellFormed } from "./wire-strings.mts";
import type { Json, JsonObject, JsonRead, JsonValue } from "./calculus.mts";
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
export function isArrayPresence(value: unknown): value is ArrayPresence {
  return value === "dense" || value === "readable" || value === "sparse";
}
export function presencePrefix(value: ArrayPresence): string {
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
/** A signature with a footprint and no promise. */
export const footprintEffect = (footprint: ClosedFootprint): Within<{ value: "any"; store: "grow" }, CallEffect> =>
  ({ footprint, promise: null, fresh: false, receiverStore: false, onThrow: false });
/** Heap preservation: no location may change, no promise. */
export const emptyEffect: CallEffect = footprintEffect(emptyFootprint);
/** An ordinary arrow's effect: every location may change, no promise. */
export const ordinaryEffect: CallEffect = footprintEffect(topFootprint);
/** A promise signature: a guard's or an assertion function's, about `param`,
 * whose code may change every location. */
export const promiseEffect = (asserts: boolean, param: number): Within<{ value: "any"; store: "grow" }, CallEffect> =>
  ({ footprint: topFootprint, promise: asserts ? { asserts: { param } } : { guards: { param } }, fresh: false,
    receiverStore: false, onThrow: false });
export const sameFootprint = (a: ClosedFootprint, b: ClosedFootprint): boolean =>
  a.value === b.value && a.store === b.store;
const samePromise = (a: CallPromise | null, b: CallPromise | null): boolean =>
  a === null || b === null ? a === b
    : a.guards !== undefined ? b.guards !== undefined && a.guards.param === b.guards.param
    : b.asserts !== undefined && a.asserts.param === b.asserts.param;
export const sameEffect = (a: CallEffect, b: CallEffect): boolean =>
  sameFootprint(a.footprint, b.footprint) && samePromise(a.promise, b.promise) && a.fresh === b.fresh &&
    a.receiverStore === b.receiverStore && a.onThrow === b.onThrow;
const isObject = (v: JsonRead): v is JsonObject =>
  typeof v === "object" && v !== null && !Array.isArray(v);
/** Whether a value is a closed footprint, as the wire states one. */
export function isClosedFootprint(value: JsonRead): value is ClosedFootprint {
  return isObject(value) && Object.keys(value).length === 2 &&
    (value.value === "keep" || value.value === "any") &&
    (value.store === "keep" || value.store === "grow" || value.store === "any");
}
/** Whether a value is a call effect, as the wire states one. */
export function isCallEffect(value: JsonRead): value is CallEffect {
  if (!isObject(value) || Object.keys(value).length !== 5 || !isClosedFootprint(value.footprint) ||
      typeof value.fresh !== "boolean" || typeof value.receiverStore !== "boolean" ||
      typeof value.onThrow !== "boolean") return false;
  const promise = value.promise;
  if (promise === null) return true;
  if (!isObject(promise) || Object.keys(promise).length !== 1) return false;
  const about: JsonRead = "guards" in promise ? promise.guards : "asserts" in promise ? promise.asserts : undefined;
  return isObject(about) && Object.keys(about).length === 1 && typeof about.param === "number" &&
    Number.isInteger(about.param) && about.param >= 0;
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
   * own. Each is left out when there are none. */
  | { refs: { first: Fields<L>; rest: Fields<L>[]; views: Fields<L>; optional?: OptionalField<L>[];
      methods?: MethodSig<L>[]; bounds?: KeyBound[] } }
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
type SchemeRow<L = number> = { scheme: { binders: L[]; signatures: Arrow<L>[];
  bounds?: [binder: L, bound: Labels<L>][]; variadic?: RestArrow<L>[];
  resolution?: { input: number; observation: number; result: number | null }[];
  /** A construct scheme: its signatures are construct signatures. */
  construct?: true } };
type MeetRow = { meet: number; clauses: Row };
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

/** Adding a clause to `Clause` without adding it here is a compile error, and
 * these are the only places a clause kind is enumerated. */
const STRING_CLAUSE_TEXT: Record<StringClause, string> = {
  nul: "null",
  bool: "boolean",
  undef: "undefined",
  num: "number",
  str: "string",
  top: "calculus top",
  source: "unknown",
  bigint: "bigint",
  symbol: "symbol",
};

/** The number a literal's bit pattern denotes. Readers show the number; the
 * bits are its identity, not its display. */
export const numberOfBits = (bits: string): number => {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  return view.getFloat64(0);
};


const isRecord = (v: JsonRead): v is JsonObject =>
  typeof v === "object" && v !== null && !Array.isArray(v);
function obj(v: JsonRead, keys: string[]): JsonObject {
  if (
    !isRecord(v) ||
    Object.keys(v).length !== keys.length ||
    keys.some((k) => !(k in v))
  )
    throw Error("unexpected type graph fields");
  return v;
}
function objOptional(
  v: JsonRead,
  keys: string[],
  optional: string[],
): JsonObject {
  if (
    !isRecord(v) ||
    keys.some((k) => !(k in v)) ||
    Object.keys(v).some((k) => !keys.includes(k) && !optional.includes(k))
  )
    throw Error("unexpected type graph fields");
  return v;
}
const isList = (v: JsonRead): v is readonly JsonValue[] => Array.isArray(v);
function array(v: JsonRead): readonly JsonValue[] {
  if (!isList(v)) throw Error("expected graph list");
  return v;
}
export function decodeLabels(v: JsonRead, size: number): Labels {
  if (
    array(v).some(
      (i) =>
        typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= size,
    )
  )
    throw Error("type graph reference out of bounds");
  // asserted: the decoder's result, checked field by field above
  return v as Labels;
}
/** The keys an index signature constrains: every string key, the canonical
 * numeric ones, or every symbol key (Lean's `IndexKeys`). */
type IndexClass = "strings" | "numeric" | "symbols";
/** An index contract: its key class and the type of each present key. */
type IndexEntry<L = number> = [IndexClass, Labels<L>];
function isIndexClass(v: unknown): v is IndexClass {
  return v === "strings" || v === "numeric" || v === "symbols";
}
/** A key as TypeScript writes it: a string plainly, a symbol by its index. */
const keyText = (name: PropertyKey): string =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;
export function decodeGraph(value: Json | undefined): TypeGraph {
  requireWellFormed(value, "type graph");
  const rows = array(value);
  const labels = (v: JsonRead) => decodeLabels(v, rows.length);
  const indexEntry = (v: JsonRead) => {
    const pair = array(v);
    if (pair.length !== 2 || !isIndexClass(pair[0]))
      throw Error("expected an index key class and its type");
    labels(pair[1]);
  };
  const contract = (v: JsonRead, hosted: boolean, rest: boolean) => {
    const sig = obj(v, ["receiver", "arguments", "result", "effect"]);
    if (hosted) obj(sig.receiver, []); else labels(sig.receiver);
    if (!isCallEffect(sig.effect)) throw Error("invalid callable effect");
    labels(sig.result);
    if (rest) {
      const args = array(sig.arguments);
      if (args.length !== 2) throw Error("expected fixed arguments and a rest contract");
      array(args[0]).forEach(labels);
      labels(args[1]);
    } else array(sig.arguments).forEach(labels);
  };
  const arrows = (v: JsonRead) => array(v).forEach((s) => contract(s, false, false));
  // Left out when empty: an explicit empty list is not the canonical form.
  const variadic = (v: JsonRead) => {
    const sigs = array(v);
    if (!sigs.length) throw Error("an empty variadic list is written by omitting it");
    sigs.forEach((s) => contract(s, false, true));
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
  const fields = (v: JsonRead, repeated = false) => {
    const names = new Set<string>();
    array(v).forEach((f) => {
      const pair = array(f);
      if (pair.length !== 2)
        throw Error("expected a field name and its labels");
      const name = keyText(key(pair[0], "a field name"));
      if (!repeated && names.has(name))
        throw Error("duplicate field in an object contract");
      names.add(name);
      labels(pair[1]);
    });
  };
  const optionalFields = (v: JsonRead) => {
    const names = new Set<string>();
    array(v).forEach((f) => {
      const r = obj(f, ["key", "readonly", "type"]);
      const name = keyText(key(r.key, "an optional field's key"));
      if (names.has(name)) throw Error("duplicate optional field in an object contract");
      names.add(name);
      if (typeof r.readonly !== "boolean") throw Error("expected an optional field's readonly flag");
      labels(r.type);
    });
  };
  const methods = (v: JsonRead) =>
    array(v).forEach((m) => {
      const r = obj(m, ["key", "calls", "rests", "schemes", "receivers"]);
      key(r.key, "a method key");
      array(r.schemes).forEach(labels);
      array(r.receivers).forEach(labels);
      array(r.calls).forEach((c) => contract(c, true, false));
      array(r.rests).forEach((c) => contract(c, true, true));
    });
  const bounds = (v: JsonRead) =>
    array(v).forEach((b) => {
      const r = obj(b, ["among", "keys"]);
      if (typeof r.among !== "boolean") throw Error("invalid key bound");
      array(r.keys).forEach((k) => key(k, "a key in a bound"));
    });
  // A record's stable keys (HOST-FAMILIES.md, "Stable keys"): a nonempty
  // list of keys, omitted when empty.
  const stableKeys = (v: JsonRead) => {
    const ks = array(v);
    if (!ks.length) throw Error("an empty stable-key list is written by omitting it");
    ks.forEach((k) => key(k, "a stable key"));
  };
  const tuple = (v: JsonRead) => {
    const t = obj(v, ["required", "optional", "rest", "readonly", "presence"]);
    if (!isArrayPresence(t.presence)) throw Error("invalid tuple density flag");
    if (typeof t.readonly !== "boolean")
      throw Error("invalid tuple readonly flag");
    array(t.required).forEach(labels);
    array(t.optional).forEach(labels);
    if (t.rest !== null) labels(t.rest);
  };
  // One validator per clause kind. A missing key does not compile, so a new
  // clause cannot reach the decoder as a silent "unknown graph clause".
  // Keyed by the language's own union, so a clause added there and not here is
  // a type error; read only at the key of `CLAUSE_KEYS` equal to the
  // document's, so a clause this does not know, `toString` among them, is a
  // refusal rather than a silent pass.
  const check: Record<ClauseKey, (body: JsonRead) => void> = {
    boolLit: (b) => {
      if (typeof obj(b, ["value"]).value !== "boolean")
        throw Error("invalid Boolean literal");
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
    },
    strLit: (b) => {
      if (typeof obj(b, ["value"]).value !== "string")
        throw Error("invalid string literal");
    },
    // Sorted and distinct, at least two: the one spelling of a set.
    numIn: (b) => {
      const bits = array(obj(b, ["bits"]).bits).map((x) => {
        if (typeof x !== "string" || !/^[0-9]+$/.test(x) || BigInt(x) > 0xffffffffffffffffn)
          throw Error("invalid number set");
        return BigInt(x);
      });
      if (bits.length < 2 || bits.some((x, i) => i > 0 && !((bits[i - 1] ?? x) < x)))
        throw Error("invalid number set");
    },
    strIn: (b) => {
      const values = array(obj(b, ["values"]).values).map((x) => {
        if (typeof x !== "string") throw Error("invalid string set");
        return x;
      });
      if (values.length < 2 || values.some((x, i) => i > 0 && !codePointLess(values[i - 1] ?? x, x)))
        throw Error("invalid string set");
    },
    bigintLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "number" || !Number.isInteger(value))
        throw Error("invalid bigint literal");
    },
    symbolLit: (b) => {
      const id = obj(b, ["id"]).id;
      if (typeof id !== "number" || !Number.isSafeInteger(id) || id < 0)
        throw Error("invalid symbol identity");
    },
    refs: (b) => {
      const r = objOptional(b, ["first", "rest", "views"], ["optional", "methods", "bounds", "stable"]);
      fields(r.first);
      array(r.rest).forEach(v => fields(v));
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      fields(r.views, true);
      if ("optional" in r) optionalFields(r.optional);
      if ("methods" in r) methods(r.methods);
      if ("bounds" in r) bounds(r.bounds);
      if ("stable" in r) stableKeys(r.stable);
    },
    dict: (b) => {
      const r = objOptional(b, ["first", "rest", "views", "indexes"], ["optional", "methods", "bounds", "cells", "stable"]);
      fields(r.first);
      array(r.rest).forEach(v => fields(v));
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      fields(r.views, true);
      array(r.indexes).forEach(indexEntry);
      if ("cells" in r) array(r.cells).forEach(indexEntry);
      if ("optional" in r) optionalFields(r.optional);
      if ("methods" in r) methods(r.methods);
      if ("bounds" in r) bounds(r.bounds);
      if ("stable" in r) stableKeys(r.stable);
    },
    ctors: (b) => {
      const r = objOptional(b, ["signatures"], ["variadic", "first", "rest", "views"]);
      if ("first" in r) fields(r.first);
      if ("rest" in r) array(r.rest).forEach(v => fields(v));
      if ("views" in r) fields(r.views, true);
      array(r.signatures).forEach((c) => contract(c, true, false));
      if ("variadic" in r) {
        const sigs = array(r.variadic);
        if (!sigs.length)
          throw Error("an empty variadic list is written by omitting it");
        sigs.forEach((c) => contract(c, true, true));
      }
    },
    list: (b) => {
      const r = obj(b, ["first", "rest"]);
      tuple(r.first);
      array(r.rest).forEach(tuple);
    },
    pack: (b) => {
      const r = obj(b, ["first", "rest"]);
      tuple(r.first);
      array(r.rest).forEach(tuple);
    },
    arrs: (b) => {
      const r = objOptional(b, ["arrows"], ["variadic"]);
      arrows(r.arrows);
      if ("variadic" in r) variadic(r.variadic);
    },
    callable: (b) => {
      const r = objOptional(b, ["first", "rest", "arrows"], ["variadic", "methods"]);
      fields(r.first);
      array(r.rest).forEach(v => fields(v));
      arrows(r.arrows);
      if ("variadic" in r) variadic(r.variadic);
      if ("methods" in r) methods(r.methods);
    },
  };

  const clauses = (row: JsonRead) =>
    array(row).forEach((c) => {
      if (typeof c === "string") {
        if (!Object.hasOwn(STRING_CLAUSE_TEXT, c)) throw Error("unknown graph clause");
        return;
      }
      if (!isRecord(c)) throw Error("unknown graph clause");
      // The clause's one key and its body, read from its own entries.
      const entries = Object.entries(c);
      const entry = entries[0];
      const kind = entry === undefined ? undefined : CLAUSE_KEYS.find((k) => k === entry[0]);
      if (entry === undefined || kind === undefined) throw Error("unknown graph clause");
      if (entries.length !== 1) throw Error("unexpected type graph fields");
      const validate = check[kind];
      validate(entry[1]);
    });
  rows.forEach((row, index) => {
    if (isRecord(row) && "meet" in row) {
      const r = obj(row, ["clauses", "meet"]);
      labels([r.meet]);
      clauses(r.clauses);
      return;
    }
    if (isRecord(row) && "param" in row) {
      const r = obj(row, ["kind", "name", "param"]);
      if ((r.kind !== "value" && r.kind !== "arguments") || typeof r.name !== "string" ||
          r.param !== index)
        throw Error("invalid parameter row");
      return;
    }
    if (isRecord(row) && "scheme" in row) {
      const r = objOptional(obj(row, ["scheme"]).scheme, ["binders", "signatures"],
        ["bounds", "variadic", "resolution", "construct"]);
      if ("construct" in r && r.construct !== true) throw Error("a scheme's construct field, when present, is true");
      array(r.binders).forEach((b) => labels([b]));
      arrows(r.signatures);
      if ("bounds" in r)
        array(r.bounds).forEach((b) => {
          const pair = array(b);
          if (pair.length !== 2) throw Error("expected a binder and its bound");
          labels([pair[0]]);
          labels(pair[1]);
        });
      if ("variadic" in r) variadic(r.variadic);
      if ("resolution" in r) {
        const owned = new Set<number>();
        const binders = array(r.binders);
        for (const group of array(r.resolution)) {
          const slots = obj(group, ["input", "observation", "result"]);
          // An awaitable group has no result slot.
          for (const slot of [slots.input, slots.observation, ...(slots.result === null ? [] : [slots.result])]) {
            if (typeof slot !== "number" || !Number.isSafeInteger(slot) || slot < 0 ||
                slot >= binders.length || owned.has(slot))
              throw Error("resolution slots must be distinct binder positions");
            owned.add(slot);
          }
        }
      }
      return;
    }
    clauses(row);
  });
  // asserted: the decoder's result, checked field by field above
  return value as TypeGraph;
}
