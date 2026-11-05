/** Native term syntax, matching Calculus.lean and its derived JSON codec. The
 * program graph over these terms is its own language, in control-flow.mts.
 *
 * The wire writes a constructor as an object with one key, the constructor's
 * name, holding its fields (a constructor without fields as its bare name).
 * The decoders here check that shape exactly and build the values below, each
 * naming its constructor in `kind` beside its own fields, so a test of `kind`
 * selects the fields the constructor has. */
/** The tags without fields, as `Tag` in Calculus.lean names them. */
const BARE_TAGS = [
  "isNul",
  "isBool",
  "isRef",
  "isFun",
  "isUndef",
  "isNullish",
  "isNum",
  "isStr",
  "isBigint",
  "isSymbol",
  "truthy",
  "isArray",
  /** `typeof v === "object"`: null, or an object without call code. */
  "typeofObject",
] as const;
type BareTag = (typeof BARE_TAGS)[number];
/** A key a tag or a merge names: a string, or a symbol's identity. */
export type Key = string | { symbol: number };
export type Tag =
  | { kind: BareTag }
  /** `key in v`: an object owning the key, a string or a symbol's identity. */
  | { kind: "hasKey"; key: Key }
  | { kind: "numEq"; bits: string }
  | { kind: "strEq"; value: string }
  | { kind: "boolEq"; value: boolean }
  /** A bigint singleton, as its integer: a JSON number of any length. */
  | { kind: "bigintEq"; value: number };
/** An object's invocation code: none, `.bind`'s forwarding descriptor, which keeps the target,
 * the receiver and the argument prefix it was given, or graph code: a
 * control-flow graph's node expressions, each node's continuation and
 * handler (as `control-flow.mts` reads them), its entry and its captures. */
export type CallCode =
  | { kind: "absent" }
  | { kind: "bound"; target: Term; receiver: Term; pre: Term[] }
  /** Graph code; `mode` is the wire's `kind`, left out for `[[Call]]` code,
   * and `rest` is left out when the code collects none, the one spelling of
   * each. */
  | { kind: "graph"; arity: number; exprs: Term[]; conts: [Json, Json][]; start: number; caps: Term[];
      mode: "construct" | "sloppy" | null; rest: boolean };
/** Every binary operator, as `Arith` in Calculus.lean names them. */
const OPERATORS = ["add", "sub", "mul", "div", "pow", "xor", "rem", "bitAnd", "bitOr", "shl", "shr", "ushr",
  "lt", "le", "gt", "ge", "eq", "looseEq"] as const;
type Operator = (typeof OPERATORS)[number];
export type Term =
  | { kind: "nul" }
  | { kind: "undef" }
  | { kind: "tru" }
  | { kind: "fls" }
  /** A number, as the bit pattern of the double it denotes: its identity. */
  | { kind: "num"; bits: string }
  /** A string, as itself. */
  | { kind: "str"; value: string }
  /** A bigint, as its integer: a JSON number of any length. */
  | { kind: "bigint"; value: number }
  /** A symbol, as its identity. */
  | { kind: "sym"; id: number }
  | { kind: "var"; i: number }
  /** Invoke `f` with the receiver `r` and the actuals `args`. */
  | { kind: "invoke"; f: Term; r: Term; args: Term[] }
  /** `new f(args)`: run `f`'s construct code with the actuals `args`. */
  | { kind: "construct"; f: Term; args: Term[] }
  | { kind: "letE"; a: Term; b: Term }
  | { kind: "objAt"; fields: [Key, number][]; call: CallCode; identity: number }
  | { kind: "makeAt"; call: CallCode; names: Key[]; inits: Term[] }
  | { kind: "readAt"; field: Key; a: Term }
  | { kind: "indexAt"; a: Term; key: Term }
  | { kind: "writeAt"; field: Key; a: Term; b: Term }
  | { kind: "test"; k: Tag; a: Term }
  | { kind: "ite"; c: Term; t: Term; e: Term }
  /** A binary operator on primitive operands: arithmetic on two numbers or
   * two bigints, or a relational comparison. */
  | { kind: "arith"; op: Operator; a: Term; b: Term }
  /** An array store with these initial elements, in order: the value an
   * array object holds in its store field. */
  | { kind: "arrLit"; inits: Term[] }
  /** The element of a store at a numeric index: `undefined` at a hole or out
   * of range. */
  | { kind: "elemAt"; a: Term; i: Term }
  /** The store with the element at a numeric index set, growing it when the
   * index is past the end. */
  | { kind: "setElem"; a: Term; i: Term; v: Term }
  /** The length of a store, as a number. */
  | { kind: "lenOf"; a: Term }
  /** A store: the location of each element, in order, or none at a hole. */
  | { kind: "arr"; elems: (number | null)[] }
  /** An actual standing for the elements of a store, read where it is written. */
  | { kind: "spread"; a: Term }
  /** Evaluate `a`, then throw its value. */
  | { kind: "throw"; a: Term }
  /** Allocate `a`'s fields and, over them, `b`'s own enumerable data
   * properties, but the keys in `drop` (an object literal's spread). */
  | { kind: "merge"; drop: Key[]; a: Term; b: Term }
  /** Evaluate `key`, then `init`, then allocate one object owning one
   * property at the key `key`'s value converts to, holding `init`'s value. */
  | { kind: "makeKey"; key: Term; init: Term }
  /** A run of graph code at the node `label`, before it is entered: the
   * code's node expressions and continuations (as in graph code), the
   * environment's slots and the value every slot past them holds. A runtime
   * form only. */
  | { kind: "goto"; exprs: Term[]; conts: [Json, Json][]; label: number; env: Term[]; dflt: Term }
  /** A run of graph code evaluating a node's instantiated expression `t`,
   * then continuing by `k`, a throw out of `t` going to `handler`. A runtime
   * form only. */
  | { kind: "frame"; exprs: Term[]; conts: [Json, Json][]; t: Term; env: Term[]; dflt: Term; k: Json; handler: Json };

/** What `JSON.parse` returns without a reviver (`ParsedJson` in
 * library-globals.mts): the decoders read the wire from it. A read of a key
 * of a parsed object finds a `Json`, or `undefined` where the object lacks
 * the key. */
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
/** A value admitted by `JsonValue` (library-globals.mts), whatever built
 * it: `null`, a Boolean, a number, a string, or a read-only array or
 * dictionary of such values. A `Json` is one. The readers of the claims, the
 * type graphs and the diagnostics take their input at it. */
export type JsonValue = null | boolean | number | string | readonly JsonValue[] | JsonObject;
/** `JsonValue`'s dictionary arm. */
export type JsonObject = { readonly [key: string]: JsonValue };
/** A read of a key of a `JsonObject`: its value, or `undefined` where the
 * object lacks the key. */
export type JsonRead = JsonValue | undefined;
/** A JSON value's array arm. */
export function isJsonList(v: JsonRead): v is Within<{ value: "keep"; store: "keep" }, readonly JsonValue[]> {
  return Array.isArray(v);
}
/** A JSON value's dictionary arm: an object that is not an array. */
export function isJsonObject(v: JsonRead): v is Within<{ value: "keep"; store: "keep" }, JsonObject> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}
/** `Json`'s dictionary arm, the same test at `JSON.parse`'s writable type. */
export function isParsedObject(v: Json | undefined): v is Within<{ value: "keep"; store: "keep" }, { [key: string]: Json }> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}
/** Whether an object holds every key of `required` as its own, and no own
 * key outside `required` and `optional`. */
export function hasExactly(
  v: object,
  required: readonly string[],
  optional: readonly string[] = [],
): Within<{ value: "keep"; store: "keep" }, boolean> {
  return (
    required.every((k) => Object.hasOwn(v, k)) &&
    Object.keys(v).every((k) => required.includes(k) || optional.includes(k))
  );
}
/** `String` of a JSON value that holds no array: a primitive or `undefined`
 * as `String` converts it; an object through `Object.prototype.toString`,
 * `"[object Object]"`, unless it owns a `toString`, which, as JSON data, is
 * not callable, so that `String` finds no callable conversion (its `valueOf`
 * returns the object) and throws a `TypeError`, with the message Node gives. */
function scalarText(value: JsonRead): Within<{ value: "any"; store: "grow" }, string> {
  if (typeof value !== "object" || value === null) return `${value}`;
  if (Object.hasOwn(value, "toString")) throw new TypeError("Cannot convert object to primitive value");
  return "[object Object]";
}
/** A position in a nested array: the list, the index of its next element,
 * and the position the list was entered from. */
interface ListPosition {
  readonly list: readonly JsonValue[];
  readonly at: number;
  readonly below: ListPosition | null;
}
/** `String` of a JSON value or an absent read. An array converts as
 * `Array.prototype.toString` joins it: its elements' conversions in order,
 * separated by commas, `null` and a hole as the empty string, an array
 * element converted the same way. The nested arrays are walked through a
 * chain of positions, so the conversion's depth costs no call stack: where
 * `String` exhausts the call stack on a deep array (a `RangeError`), this
 * returns the text. Every other result and exception is `String`'s. */
export function stringOfJson(value: JsonRead): Within<{ value: "any"; store: "grow" }, string> {
  if (value === undefined || !isJsonList(value)) return scalarText(value);
  let text = "";
  let position: ListPosition | null = { list: value, at: 0, below: null };
  while (position !== null) {
    const list = position.list;
    const at = position.at;
    const below: ListPosition | null = position.below;
    if (at >= list.length) {
      position = below;
      continue;
    }
    if (at > 0) text += ",";
    const next: ListPosition = { list, at: at + 1, below };
    const element: JsonRead = list[at];
    if (element !== undefined && element !== null && isJsonList(element))
      position = { list: element, at: 0, below: next };
    else {
      if (element !== undefined && element !== null) text += scalarText(element);
      position = next;
    }
  }
  return text;
}
/* JSON shape checks, shared with the program graph in control-flow.mts. They
 * belong to neither language, so they name neither: a malformed target is not
 * a malformed term. */
export function fields(v: Json | undefined, keys: string[]): { [key: string]: Json } {
  if (!isParsedObject(v) || !hasExactly(v, keys)) throw Error("unexpected or missing field");
  return v;
}
/** A non-negative integer. */
export function nat(v: unknown): Within<{ value: "keep"; store: "keep" }, number> {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0)
    throw Error("expected a non-negative integer");
  return v;
}
/** The one key of a constructor written as an object, and what it holds. */
export function constructorOf(v: Json | undefined): { key: string; value: Json } {
  if (!isParsedObject(v)) throw Error("invalid constructor");
  const entries = Object.entries(v);
  const entry = entries[0];
  if (entries.length !== 1 || entry === undefined) throw Error("unexpected or missing field");
  const [key, value] = entry;
  return { key, value };
}
/** A double's bit pattern: decimal, unsigned, at most 64 bits. */
function bitsOf(v: Json | undefined): string {
  if (typeof v !== "string" || !/^[0-9]+$/.test(v) || BigInt(v) > 0xffffffffffffffffn)
    throw Error("invalid number");
  return v;
}
function stringOf(v: Json | undefined, what: string): string {
  if (typeof v !== "string") throw Error(what);
  return v;
}
function termsOf(v: Json | undefined): Term[] {
  if (!Array.isArray(v)) throw Error("invalid arguments");
  return v.map(decodeTerm);
}
/** A property key: a string as itself, a symbol as `{"symbol": id}`. */
function keyOf(v: Json | undefined): Key {
  if (typeof v === "string") return v;
  return { symbol: nat(fields(v, ["symbol"]).symbol) };
}
/** Graph code's continuations: one pair of a continuation and a handler per
 * node expression. */
function continuationsOf(v: Json | undefined, nodes: number): [Json, Json][] {
  if (!Array.isArray(v) || v.length !== nodes) throw Error("invalid graph code");
  return v.map((k: Json): [Json, Json] => {
    if (!Array.isArray(k) || k.length !== 2) throw Error("invalid graph code");
    const [continuation, handler] = k;
    if (continuation === undefined || handler === undefined) throw Error("invalid graph code");
    return [continuation, handler];
  });
}

export function decodeTag(v: Json | undefined): Tag {
  const bare = BARE_TAGS.find((t) => t === v);
  if (bare !== undefined) return { kind: bare };
  const { key, value } = constructorOf(v);
  switch (key) {
    case "hasKey": {
      const k = fields(value, ["key"]).key;
      if (typeof k !== "string" && !(isParsedObject(k) && Object.keys(k).length === 1 && typeof k.symbol === "number"))
        throw Error("unknown tag");
      return { kind: "hasKey", key: keyOf(k) };
    }
    case "numEq": {
      const b = fields(value, ["bits"]).bits;
      if (typeof b !== "string" || !/^[0-9]+$/.test(b) || BigInt(b) > 0xffffffffffffffffn) throw Error("unknown tag");
      return { kind: "numEq", bits: b };
    }
    case "strEq": {
      const s = fields(value, ["value"]).value;
      if (typeof s !== "string") throw Error("unknown tag");
      return { kind: "strEq", value: s };
    }
    case "boolEq": {
      const b = fields(value, ["value"]).value;
      if (typeof b !== "boolean") throw Error("unknown tag");
      return { kind: "boolEq", value: b };
    }
    case "bigintEq": {
      const n = fields(value, ["value"]).value;
      if (typeof n !== "number") throw Error("unknown tag");
      return { kind: "bigintEq", value: n };
    }
    default:
      throw Error("unknown tag");
  }
}

function decodeCode(v: Json | undefined): CallCode {
  if (v === "absent") return { kind: "absent" };
  const { key, value } = constructorOf(v);
  switch (key) {
    case "bound": {
      const c = fields(value, ["target", "receiver", "pre"]);
      const target = decodeTerm(c.target), receiver = decodeTerm(c.receiver);
      if (!Array.isArray(c.pre)) throw Error("invalid bound prefix");
      return { kind: "bound", target, receiver, pre: c.pre.map(decodeTerm) };
    }
    case "graph": {
      const optional = isParsedObject(value) ? ["kind", "rest"].filter((k) => k in value) : [];
      const c = fields(value, ["arity", "exprs", "conts", "start", "caps", ...optional]);
      let mode: "construct" | "sloppy" | null = null;
      if ("kind" in c) {
        if (c.kind === "construct" || c.kind === "sloppy") mode = c.kind;
        else throw Error("invalid code kind");
      }
      if ("rest" in c && c.rest !== true) throw Error("invalid code rest flag");
      const arity = nat(c.arity), start = nat(c.start);
      const { exprs, conts, caps } = c;
      if (!Array.isArray(exprs) || !Array.isArray(caps)) throw Error("invalid graph code");
      const pairs = continuationsOf(conts, exprs.length);
      return { kind: "graph", arity, exprs: exprs.map(decodeTerm), conts: pairs, start, caps: caps.map(decodeTerm),
        mode, rest: "rest" in c };
    }
    default:
      throw Error("unknown call code");
  }
}

export function decodeTerm(v: Json | undefined): Term {
  switch (v) {
    case "nul": return { kind: "nul" };
    case "undef": return { kind: "undef" };
    case "tru": return { kind: "tru" };
    case "fls": return { kind: "fls" };
  }
  if (!v || typeof v !== "object") throw Error("invalid term");
  const { key, value } = constructorOf(v);
  switch (key) {
    case "num": return { kind: "num", bits: bitsOf(fields(value, ["bits"]).bits) };
    case "str": return { kind: "str", value: stringOf(fields(value, ["value"]).value, "invalid string") };
    case "bigint": {
      const n = fields(value, ["value"]).value;
      if (typeof n !== "number" || !Number.isInteger(n)) throw Error("invalid bigint");
      return { kind: "bigint", value: n };
    }
    case "sym": return { kind: "sym", id: nat(fields(value, ["id"]).id) };
    case "var": return { kind: "var", i: nat(fields(value, ["i"]).i) };
    case "invoke": {
      const o = fields(value, ["f", "r", "args"]);
      return { kind: "invoke", f: decodeTerm(o.f), r: decodeTerm(o.r), args: termsOf(o.args) };
    }
    case "construct": {
      const o = fields(value, ["f", "args"]);
      return { kind: "construct", f: decodeTerm(o.f), args: termsOf(o.args) };
    }
    case "letE": {
      const o = fields(value, ["a", "b"]);
      return { kind: "letE", a: decodeTerm(o.a), b: decodeTerm(o.b) };
    }
    case "objAt": {
      const o = fields(value, ["fields", "call", "identity"]);
      if (!Array.isArray(o.fields)) throw Error("invalid object fields");
      const pairs: [Key, number][] = o.fields.map((pair: Json): [Key, number] => {
        if (!Array.isArray(pair) || pair.length !== 2) throw Error("invalid object field");
        const [name, location] = pair;
        return [keyOf(name), nat(location)];
      });
      return { kind: "objAt", fields: pairs, call: decodeCode(o.call), identity: nat(o.identity) };
    }
    case "makeAt": {
      const o = fields(value, ["call", "names", "inits"]);
      const call = decodeCode(o.call);
      const names = o.names;
      if (!Array.isArray(names)) throw Error("invalid field names");
      return { kind: "makeAt", call, names: names.map(keyOf), inits: termsOf(o.inits) };
    }
    case "readAt": {
      const o = fields(value, ["field", "a"]);
      return { kind: "readAt", field: keyOf(o.field), a: decodeTerm(o.a) };
    }
    case "indexAt": {
      const o = fields(value, ["a", "key"]);
      return { kind: "indexAt", a: decodeTerm(o.a), key: decodeTerm(o.key) };
    }
    case "writeAt": {
      const o = fields(value, ["field", "a", "b"]);
      return { kind: "writeAt", field: keyOf(o.field), a: decodeTerm(o.a), b: decodeTerm(o.b) };
    }
    case "test": {
      const o = fields(value, ["k", "a"]);
      return { kind: "test", k: decodeTag(o.k), a: decodeTerm(o.a) };
    }
    case "ite": {
      const o = fields(value, ["c", "t", "e"]);
      return { kind: "ite", c: decodeTerm(o.c), t: decodeTerm(o.t), e: decodeTerm(o.e) };
    }
    case "arith": {
      const o = fields(value, ["op", "a", "b"]);
      const op = OPERATORS.find((x) => x === o.op);
      if (op === undefined) throw Error("unknown binary operator");
      return { kind: "arith", op, a: decodeTerm(o.a), b: decodeTerm(o.b) };
    }
    case "arrLit": return { kind: "arrLit", inits: termsOf(fields(value, ["inits"]).inits) };
    case "elemAt": {
      const o = fields(value, ["a", "i"]);
      return { kind: "elemAt", a: decodeTerm(o.a), i: decodeTerm(o.i) };
    }
    case "setElem": {
      const o = fields(value, ["a", "i", "v"]);
      return { kind: "setElem", a: decodeTerm(o.a), i: decodeTerm(o.i), v: decodeTerm(o.v) };
    }
    case "lenOf": return { kind: "lenOf", a: decodeTerm(fields(value, ["a"]).a) };
    case "arr": {
      const elems = fields(value, ["elems"]).elems;
      if (!Array.isArray(elems)) throw Error("invalid store");
      return { kind: "arr", elems: elems.map((l: Json) => (l === null ? null : nat(l))) };
    }
    case "spread": return { kind: "spread", a: decodeTerm(fields(value, ["a"]).a) };
    case "throw": return { kind: "throw", a: decodeTerm(fields(value, ["a"]).a) };
    case "merge": {
      const o = fields(value, ["drop", "a", "b"]);
      const drop = o.drop;
      if (!Array.isArray(drop)) throw Error("invalid dropped keys");
      return { kind: "merge", drop: drop.map(keyOf), a: decodeTerm(o.a), b: decodeTerm(o.b) };
    }
    case "makeKey": {
      const o = fields(value, ["key", "init"]);
      return { kind: "makeKey", key: decodeTerm(o.key), init: decodeTerm(o.init) };
    }
    case "goto": {
      const o = fields(value, ["exprs", "conts", "label", "env", "dflt"]);
      const exprs = termsOf(o.exprs);
      return { kind: "goto", exprs, conts: continuationsOf(o.conts, exprs.length), label: nat(o.label),
        env: termsOf(o.env), dflt: decodeTerm(o.dflt) };
    }
    case "frame": {
      const o = fields(value, ["exprs", "conts", "t", "env", "dflt", "k", "handler"]);
      const exprs = termsOf(o.exprs);
      const { k, handler } = o;
      if (k === undefined || handler === undefined) throw Error("invalid frame");
      return { kind: "frame", exprs, conts: continuationsOf(o.conts, exprs.length), t: decodeTerm(o.t),
        env: termsOf(o.env), dflt: decodeTerm(o.dflt), k, handler };
    }
    default:
      throw Error("unknown term constructor");
  }
}

/* Readable notation for terms, as commit records and the lowering dump show
 * them. Each is a case analysis over its type's `kind`, exhaustive: adding a
 * constructor to `Term`, `Tag` or `CallCode` and not here is a type error. */
/** No value reaches this: its argument's type has no member left. */
export function unmatched(x: never): never {
  throw Error(`a value of no known constructor: ${JSON.stringify(x)}`);
}
const showTerms = (ts: Term[]): string => ts.map(showTerm).join(", ");
/** A term in the notation of commit records. */
export function showTerm(t: Term): string {
  switch (t.kind) {
    case "nul": return "null";
    case "undef": return "undefined";
    case "tru": return "true";
    case "fls": return "false";
    case "num": return `num#${t.bits}`;
    case "str": return JSON.stringify(t.value);
    case "bigint": return `${t.value}n`;
    case "sym": return `sym#${t.id}`;
    case "var": return `x${t.i}`;
    case "invoke": return `${showTerm(t.f)}.call(${[t.r, ...t.args].map(showTerm).join(", ")})`;
    case "construct": return `new ${showTerm(t.f)}(${showTerms(t.args)})`;
    case "letE": return `let ${showTerm(t.a)} in ${showTerm(t.b)}`;
    case "objAt": return `obj#${t.identity}{${t.fields.map(([k, l]) => `${showKey(k)}: ℓ${l}`).join(", ")}}${showCode(t.call)}`;
    case "makeAt": {
      const inits = t.inits;
      return `new{${t.names.map((n, i) => {
        const init = inits[i];
        return `${showKey(n)}: ${init === undefined ? "?" : showTerm(init)}`;
      }).join(", ")}}${showCode(t.call)}`;
    }
    case "readAt": return `${showTerm(t.a)}.${showKey(t.field)}`;
    case "indexAt": return `${showTerm(t.a)}[${showTerm(t.key)}]`;
    case "writeAt": return `${showTerm(t.a)}.${showKey(t.field)} := ${showTerm(t.b)}`;
    case "test": return `${showTag(t.k)}(${showTerm(t.a)})`;
    case "ite": return `if ${showTerm(t.c)} then ${showTerm(t.t)} else ${showTerm(t.e)}`;
    case "arith": return `${showTerm(t.a)} ${t.op} ${showTerm(t.b)}`;
    case "arrLit": return `[${showTerms(t.inits)}]`;
    case "elemAt": return `${showTerm(t.a)}⟦${showTerm(t.i)}⟧`;
    case "setElem": return `${showTerm(t.a)}⟦${showTerm(t.i)} ↦ ${showTerm(t.v)}⟧`;
    case "lenOf": return `len(${showTerm(t.a)})`;
    case "arr": return `store[${t.elems.map((e) => (e === null ? "hole" : `ℓ${e}`)).join(", ")}]`;
    case "spread": return `...${showTerm(t.a)}`;
    case "throw": return `throw ${showTerm(t.a)}`;
    case "makeKey": return `makeKey(${showTerm(t.key)}, ${showTerm(t.init)})`;
    case "merge": {
      const drop = t.drop.length ? ` drop ${t.drop.map(showKey).join(", ")}` : "";
      return `merge(${showTerm(t.a)}, ${showTerm(t.b)}${drop})`;
    }
    case "goto": return `goto ℓ${t.label} in graph of ${t.exprs.length} nodes`;
    case "frame": return `frame(${showTerm(t.t)}) in graph of ${t.exprs.length} nodes`;
    default: return unmatched(t);
  }
}
const showKey = (k: Key): string => (typeof k === "string" ? k : `sym#${k.symbol}`);
export function showTag(k: Tag): string {
  switch (k.kind) {
    case "isNul": return "isNull";
    case "isBool": return "isBoolean";
    case "isRef": return "isObject";
    case "isFun": return "isFunction";
    case "isUndef": return "isUndefined";
    case "isNullish": return "isNullish";
    case "isNum": return "isNumber";
    case "isStr": return "isString";
    case "isBigint": return "isBigInt";
    case "isSymbol": return "isSymbol";
    case "truthy": return "truthy";
    case "isArray": return "Array.isArray";
    case "typeofObject": return "typeofObject";
    case "hasKey": return `has ${showKey(k.key)}`;
    case "numEq": return `=== num#${k.bits}`;
    case "strEq": return `=== ${JSON.stringify(k.value)}`;
    case "boolEq": return `=== ${k.value}`;
    case "bigintEq": return `=== ${k.value}n`;
    default: return unmatched(k);
  }
}
function showCode(c: CallCode): string {
  switch (c.kind) {
    case "absent": return "";
    case "bound": return ` code(bind ${showTerm(c.target)})`;
    case "graph": return ` code(graph of ${c.exprs.length} nodes)`;
    default: return unmatched(c);
  }
}
