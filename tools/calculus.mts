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
/** An object's invocation code: none, a closure, variadic code collecting
 * further actuals, `.bind`'s forwarding descriptor, which keeps the target,
 * the receiver and the argument prefix it was given, or graph code: a
 * control-flow graph's node expressions, each node's continuation and
 * handler (as `control-flow.mts` reads them), its entry and its captures. */
export type CallCode =
  | { kind: "absent" }
  | { kind: "closure"; arity: number; body: Term }
  | { kind: "variadic"; fixed: number; body: Term }
  | { kind: "bound"; target: Term; receiver: Term; pre: Term[] }
  /** Graph code; `mode` is the wire's `kind`, left out for `[[Call]]` code,
   * and `rest` is left out when the code collects none, the one spelling of
   * each. */
  | { kind: "graph"; arity: number; exprs: Term[]; conts: [Json, Json][]; start: number; caps: Term[];
      mode: "construct" | "sloppy" | null; rest: boolean };
/** Every binary operator, as `Arith` in Calculus.lean names them. */
const OPERATORS = ["add", "sub", "mul", "div", "pow", "xor", "rem", "bitAnd", "bitOr", "shl", "shr", "ushr",
  "lt", "le", "gt", "ge", "eq"] as const;
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
  | { kind: "var"; i: number }
  /** Invoke `f` with the receiver `r` and the actuals `args`. */
  | { kind: "invoke"; f: Term; r: Term; args: Term[] }
  /** `new f(args)`: run `f`'s construct code with the actuals `args`. */
  | { kind: "construct"; f: Term; args: Term[] }
  | { kind: "letE"; a: Term; b: Term }
  | { kind: "objAt"; fields: [string, number][]; call: CallCode; identity: number }
  | { kind: "makeAt"; call: CallCode; names: string[]; inits: Term[] }
  | { kind: "readAt"; field: string; a: Term }
  | { kind: "indexAt"; a: Term; key: Term }
  | { kind: "writeAt"; field: string; a: Term; b: Term }
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
  | { kind: "makeKey"; key: Term; init: Term };

/** What `JSON.parse` returns without a reviver (`ParsedJson` in
 * library-globals.mts): the decoders read the wire from it. A read of a key
 * of a parsed object finds a `Json`, or `undefined` where the object lacks
 * the key. */
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
/* JSON shape checks, shared with the program graph in control-flow.mts. They
 * belong to neither language, so they name neither: a malformed target is not
 * a malformed term. */
function isRecord(v: Json | undefined): v is { [key: string]: Json } {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
export function fields(v: Json | undefined, keys: string[]): { [key: string]: Json } {
  if (
    !isRecord(v) ||
    Object.keys(v).length !== keys.length ||
    keys.some((k) => !(k in v))
  )
    throw Error("unexpected or missing field");
  return v;
}
/** A non-negative integer. */
export function nat(v: Json | undefined): number {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0)
    throw Error("expected a non-negative integer");
  return v;
}
/** The one key of a constructor written as an object, and what it holds. */
export function constructorOf(v: Json | undefined): { key: string; value: Json } {
  if (!isRecord(v)) throw Error("invalid constructor");
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
function keyOf(v: Json | undefined): Key {
  if (typeof v === "string") return v;
  const s = fields(v, ["symbol"]).symbol;
  if (typeof s !== "number") throw Error("invalid symbol key");
  return { symbol: s };
}

export function decodeTag(v: Json | undefined): Tag {
  const bare = BARE_TAGS.find((t) => t === v);
  if (bare !== undefined) return { kind: bare };
  const { key, value } = constructorOf(v);
  switch (key) {
    case "hasKey": {
      const k = fields(value, ["key"]).key;
      if (typeof k !== "string" && !(isRecord(k) && Object.keys(k).length === 1 && typeof k.symbol === "number"))
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
    case "closure": {
      const c = fields(value, ["arity", "body"]);
      return { kind: "closure", arity: nat(c.arity), body: decodeTerm(c.body) };
    }
    case "variadic": {
      const c = fields(value, ["fixed", "body"]);
      return { kind: "variadic", fixed: nat(c.fixed), body: decodeTerm(c.body) };
    }
    case "bound": {
      const c = fields(value, ["target", "receiver", "pre"]);
      const target = decodeTerm(c.target), receiver = decodeTerm(c.receiver);
      if (!Array.isArray(c.pre)) throw Error("invalid bound prefix");
      return { kind: "bound", target, receiver, pre: c.pre.map(decodeTerm) };
    }
    case "graph": {
      const optional = isRecord(value) ? ["kind", "rest"].filter((k) => k in value) : [];
      const c = fields(value, ["arity", "exprs", "conts", "start", "caps", ...optional]);
      let mode: "construct" | "sloppy" | null = null;
      if ("kind" in c) {
        if (c.kind === "construct" || c.kind === "sloppy") mode = c.kind;
        else throw Error("invalid code kind");
      }
      if ("rest" in c && c.rest !== true) throw Error("invalid code rest flag");
      const arity = nat(c.arity), start = nat(c.start);
      const { exprs, conts, caps } = c;
      if (!Array.isArray(exprs) || !Array.isArray(conts) || !Array.isArray(caps) || exprs.length !== conts.length)
        throw Error("invalid graph code");
      const pairs: [Json, Json][] = conts.map((k: Json): [Json, Json] => {
        if (!Array.isArray(k) || k.length !== 2) throw Error("invalid graph code");
        const [continuation, handler] = k;
        if (continuation === undefined || handler === undefined) throw Error("invalid graph code");
        return [continuation, handler];
      });
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
      const pairs: [string, number][] = o.fields.map((pair: Json): [string, number] => {
        if (!Array.isArray(pair) || pair.length !== 2) throw Error("invalid object field");
        const [name, location] = pair;
        if (typeof name !== "string") throw Error("invalid object field");
        return [name, nat(location)];
      });
      return { kind: "objAt", fields: pairs, call: decodeCode(o.call), identity: nat(o.identity) };
    }
    case "makeAt": {
      const o = fields(value, ["call", "names", "inits"]);
      const call = decodeCode(o.call);
      const names = o.names;
      if (!Array.isArray(names)) throw Error("invalid field names");
      const strings = names.map((n: Json) => stringOf(n, "invalid field names"));
      return { kind: "makeAt", call, names: strings, inits: termsOf(o.inits) };
    }
    case "readAt": {
      const o = fields(value, ["field", "a"]);
      return { kind: "readAt", field: stringOf(o.field, "invalid field name"), a: decodeTerm(o.a) };
    }
    case "indexAt": {
      const o = fields(value, ["a", "key"]);
      return { kind: "indexAt", a: decodeTerm(o.a), key: decodeTerm(o.key) };
    }
    case "writeAt": {
      const o = fields(value, ["field", "a", "b"]);
      return { kind: "writeAt", field: stringOf(o.field, "invalid field name"), a: decodeTerm(o.a), b: decodeTerm(o.b) };
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
      if (!Array.isArray(drop) || drop.some((key: Json) => typeof key !== "string" &&
          !(isRecord(key) && Object.keys(key).length === 1 && typeof key.symbol === "number")))
        throw Error("invalid dropped keys");
      return { kind: "merge", drop: drop.map(keyOf), a: decodeTerm(o.a), b: decodeTerm(o.b) };
    }
    case "makeKey": {
      const o = fields(value, ["key", "init"]);
      return { kind: "makeKey", key: decodeTerm(o.key), init: decodeTerm(o.init) };
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
    case "var": return `x${t.i}`;
    case "invoke": return `${showTerm(t.f)}.call(${[t.r, ...t.args].map(showTerm).join(", ")})`;
    case "construct": return `new ${showTerm(t.f)}(${showTerms(t.args)})`;
    case "letE": return `let ${showTerm(t.a)} in ${showTerm(t.b)}`;
    case "objAt": return `obj#${t.identity}{${t.fields.map(([k, l]) => `${k}: ℓ${l}`).join(", ")}}${showCode(t.call)}`;
    case "makeAt": {
      const inits = t.inits;
      return `new{${t.names.map((n, i) => {
        const init = inits[i];
        return `${n}: ${init === undefined ? "?" : showTerm(init)}`;
      }).join(", ")}}${showCode(t.call)}`;
    }
    case "readAt": return `${showTerm(t.a)}.${t.field}`;
    case "indexAt": return `${showTerm(t.a)}[${showTerm(t.key)}]`;
    case "writeAt": return `${showTerm(t.a)}.${t.field} := ${showTerm(t.b)}`;
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
    case "closure": return ` code(λ${c.arity}. ${showTerm(c.body)})`;
    case "variadic": return ` code(λ${c.fixed}+. ${showTerm(c.body)})`;
    case "bound": return ` code(bind ${showTerm(c.target)})`;
    case "graph": return ` code(graph of ${c.exprs.length} nodes)`;
    default: return unmatched(c);
  }
}
