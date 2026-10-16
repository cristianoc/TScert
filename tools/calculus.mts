/** Native term syntax, matching Calculus.lean and its derived JSON codec. The
 * program graph over these terms is its own language, in control-flow.mts. */
export type Tag =
  | "isNul"
  | "isBool"
  | "isRef"
  | "isFun"
  | "isUndef"
  | "isNullish"
  | "isNum"
  | "isStr"
  | "isBigint"
  | "isSymbol"
  | "truthy"
  | "isArray"
  /** `typeof v === "object"`: null, or an object without call code. */
  | "typeofObject"
  /** `key in v`: an object owning the key, a string or a symbol's identity. */
  | { hasKey: { key: string | { symbol: number } } }
  | { numEq: { bits: string } }
  | { strEq: { value: string } }
  | { boolEq: { value: boolean } }
  /** A bigint singleton, as its integer: a JSON number of any length. */
  | { bigintEq: { value: number } };
/** An object's invocation code: none, a closure, variadic code collecting
 * further actuals, `.bind`'s forwarding descriptor, which keeps the target,
 * the receiver and the argument prefix it was given, or graph code: a
 * control-flow graph's node expressions, each node's continuation and
 * handler (as `control-flow.mts` reads them), its entry and its captures. */
type CallCode =
  | "absent"
  | { closure: { arity: number; body: Term } }
  | { variadic: { fixed: number; body: Term } }
  | { bound: { target: Term; receiver: Term; pre: Term[] } }
  | { graph: { arity: number; exprs: Term[]; conts: [unknown, unknown][]; start: number; caps: Term[] } };
export type Term =
  | "nul"
  | "undef"
  | "tru"
  | "fls"
  /** A number, as the bit pattern of the double it denotes: its identity. */
  | { num: { bits: string } }
  /** A string, as itself. */
  | { str: { value: string } }
  /** A bigint, as its integer: a JSON number of any length. */
  | { bigint: { value: number } }
  | { var: { i: number } }
  /** Invoke `f` with the receiver `r` and the actuals `args`. */
  | { invoke: { f: Term; r: Term; args: Term[] } }
  | { letE: { a: Term; b: Term } }
  | { objAt: { fields: [string, number][]; call: CallCode; identity: number } }
  | { makeAt: { call: CallCode; names: string[]; inits: Term[] } }
  | { readAt: { field: string; a: Term } }
  | { indexAt: { a: Term; key: Term } }
  | { writeAt: { field: string; a: Term; b: Term } }
  | { test: { k: Tag; a: Term } }
  | { ite: { c: Term; t: Term; e: Term } }
  /** A binary operator on primitive operands: arithmetic on two numbers or
   * two bigints, or a relational comparison. */
  | { arith: { op: (typeof OPERATORS)[number]; a: Term; b: Term } }
  /** An array store with these initial elements, in order: the value an
   * array object holds in its store field. */
  | { arrLit: { inits: Term[] } }
  /** The element of a store at a numeric index: `undefined` at a hole or out
   * of range. */
  | { elemAt: { a: Term; i: Term } }
  /** The store with the element at a numeric index set, growing it when the
   * index is past the end. */
  | { setElem: { a: Term; i: Term; v: Term } }
  /** The length of a store, as a number. */
  | { lenOf: { a: Term } }
  /** A store: the location of each element, in order, or none at a hole. */
  | { arr: { elems: (number | null)[] } }
  /** An actual standing for the elements of a store, read where it is written. */
  | { spread: { a: Term } }
  /** Evaluate `a`, then throw its value. */
  | { throw: { a: Term } }
  /** Allocate `a`'s fields and, over them, `b`'s own enumerable data
   * properties, but the keys in `drop` (an object literal's spread). */
  | { merge: { drop: (string | { symbol: number })[]; a: Term; b: Term } }
  /** Evaluate `key`, then `init`, then allocate one object owning one
   * property at the key `key`'s value converts to, holding `init`'s value. */
  | { makeKey: { key: Term; init: Term } };
/** Every binary operator, as `Arith` in Calculus.lean names them. */
const OPERATORS = ["add", "sub", "mul", "div", "pow", "xor", "rem", "lt", "le", "gt", "ge", "eq"] as const;
/** Every tag, checked against `Tag`: adding one there and not here is a type
 * error rather than an "unknown tag" at run time. */
const TAGS: Record<Extract<Tag, string>, true> = {
  isNul: true,
  isBool: true,
  isRef: true,
  isFun: true,
  isUndef: true,
  isNullish: true,
  isNum: true,
  isStr: true,
  isBigint: true,
  isSymbol: true,
  truthy: true,
  isArray: true,
  typeofObject: true,
};
const tags: readonly unknown[] = Object.keys(TAGS);
/** Whether a decoded value is a tag, so the table above stays the one place a
 * tag is declared even for readers of other languages that carry one. */
export function isTag(v: unknown): v is Tag {
  if (tags.includes(v)) return true;
  if (!isRecord(v) || Object.keys(v).length !== 1) return false;
  if (isRecord(v.strEq))
    return (
      Object.keys(v.strEq).length === 1 && typeof v.strEq.value === "string"
    );
  if (isRecord(v.boolEq))
    return (
      Object.keys(v.boolEq).length === 1 && typeof v.boolEq.value === "boolean"
    );
  if (isRecord(v.hasKey)) {
    const key = v.hasKey.key;
    return (
      Object.keys(v.hasKey).length === 1 &&
      (typeof key === "string" ||
        (isRecord(key) && Object.keys(key).length === 1 && typeof key.symbol === "number"))
    );
  }
  if (isRecord(v.bigintEq))
    return (
      Object.keys(v.bigintEq).length === 1 && typeof v.bigintEq.value === "number"
    );
  if (!isRecord(v.numEq)) return false;
  const n = v.numEq;
  return (
    Object.keys(n).length === 1 &&
    typeof n.bits === "string" &&
    /^[0-9]+$/.test(n.bits) &&
    BigInt(n.bits) <= 0xffffffffffffffffn
  );
}
/* JSON shape checks, shared with the program graph in control-flow.mts. They
 * belong to neither language, so they name neither: a malformed target is not
 * a malformed term. */
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
export function fields(v: unknown, keys: string[]): Record<string, unknown> {
  if (
    !isRecord(v) ||
    Object.keys(v).length !== keys.length ||
    keys.some((k) => !(k in v))
  )
    throw Error("unexpected or missing field");
  return v;
}
export function nat(v: unknown) {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0)
    throw Error("expected a non-negative integer");
}
function code(v: unknown) {
  if (v === "absent") return;
  const key = isRecord(v) ? Object.keys(v)[0] : undefined;
  if (key === "closure") {
    const c = fields(fields(v, ["closure"]).closure, ["arity", "body"]);
    nat(c.arity);
    decodeTerm(c.body);
  } else if (key === "variadic") {
    const c = fields(fields(v, ["variadic"]).variadic, ["fixed", "body"]);
    nat(c.fixed);
    decodeTerm(c.body);
  } else if (key === "bound") {
    const c = fields(fields(v, ["bound"]).bound, ["target", "receiver", "pre"]);
    decodeTerm(c.target);
    decodeTerm(c.receiver);
    if (!Array.isArray(c.pre)) throw Error("invalid bound prefix");
    c.pre.forEach(decodeTerm);
  } else if (key === "graph") {
    const c = fields(fields(v, ["graph"]).graph, ["arity", "exprs", "conts", "start", "caps"]);
    nat(c.arity);
    nat(c.start);
    if (!Array.isArray(c.exprs) || !Array.isArray(c.conts) || !Array.isArray(c.caps) ||
        c.exprs.length !== c.conts.length || !c.conts.every((k) => Array.isArray(k) && k.length === 2))
      throw Error("invalid graph code");
    c.exprs.forEach(decodeTerm);
    c.caps.forEach(decodeTerm);
  } else throw Error("unknown call code");
}
/** The terms that are all tag and no fields, which is how they are written. */
const BARE: Record<Extract<Term, string>, true> = {
  nul: true,
  undef: true,
  tru: true,
  fls: true,
};
const bare: readonly unknown[] = Object.keys(BARE);
const isBareTerm = (v: unknown): v is Extract<Term, string> => bare.includes(v);
export type KeysOf<T> = T extends unknown ? keyof T : never;
type TermKey = KeysOf<Exclude<Term, string>>;

export function decodeTerm(value: unknown): Term {
  if (isBareTerm(value)) return value;
  if (!value || typeof value !== "object") throw Error("invalid term");
  const key = Object.keys(value)[0],
    outer = fields(value, [key]);
  // One entry per compound constructor of `Term`; a missing key is a type error.
  // Keyed by the language's own union, so a constructor added there and not
  // here is a type error; read by a key that may be none of them, so a
  // constructor this does not know is a refusal.
  const shape: Record<TermKey, string[]> &
    Record<string, string[] | undefined> = {
    num: ["bits"],
    str: ["value"],
    bigint: ["value"],
    var: ["i"],
    invoke: ["f", "r", "args"],
    letE: ["a", "b"],
    objAt: ["fields", "call", "identity"],
    makeAt: ["call", "names", "inits"],
    readAt: ["field", "a"],
    indexAt: ["a", "key"],
    writeAt: ["field", "a", "b"],
    test: ["k", "a"],
    ite: ["c", "t", "e"],
    arith: ["op", "a", "b"],
    arrLit: ["inits"],
    elemAt: ["a", "i"],
    setElem: ["a", "i", "v"],
    lenOf: ["a"],
    arr: ["elems"],
    spread: ["a"],
    throw: ["a"],
    merge: ["drop", "a", "b"],
    makeKey: ["key", "init"],
  };
  const keys = shape[key];
  if (!keys) throw Error("unknown term constructor");
  const o = fields(outer[key], keys);
  for (const [k, v] of Object.entries(o)) {
    // A number's identity is its double's bit pattern, decimal, unsigned 64.
    if (k === "bits") {
      if (
        typeof v !== "string" ||
        !/^[0-9]+$/.test(v) ||
        BigInt(v) > 0xffffffffffffffffn
      )
        throw Error("invalid number");
    } else if (k === "value" && key === "bigint") {
      if (typeof v !== "number" || !Number.isInteger(v)) throw Error("invalid bigint");
    } else if (k === "value") {
      if (typeof v !== "string") throw Error("invalid string");
    } else if (k === "i" || k === "l") nat(v);
    else if (k === "call") code(v);
    else if (k === "k") {
      if (!isTag(v)) throw Error("unknown tag");
    } else if (k === "field") {
      if (typeof v !== "string") throw Error("invalid field name");
    } else if (k === "names") {
      if (!Array.isArray(v) || v.some((n) => typeof n !== "string"))
        throw Error("invalid field names");
    } else if (k === "fields") {
      if (!Array.isArray(v)) throw Error("invalid object fields");
      for (const pair of v) {
        if (
          !Array.isArray(pair) ||
          pair.length !== 2 ||
          typeof pair[0] !== "string"
        )
          throw Error("invalid object field");
        nat(pair[1]);
      }
    } else if (k === "op") {
      if (!OPERATORS.some((op) => op === v))
        throw Error("unknown binary operator");
    } else if (k === "elems") {
      if (!Array.isArray(v)) throw Error("invalid store");
      for (const l of v) if (l !== null) nat(l);
    } else if (k === "drop") {
      if (!Array.isArray(v) || v.some((key) => typeof key !== "string" &&
          !(isRecord(key) && Object.keys(key).length === 1 && typeof key.symbol === "number")))
        throw Error("invalid dropped keys");
    } else if (k === "args" || k === "inits") {
      if (!Array.isArray(v)) throw Error("invalid arguments");
      v.forEach(decodeTerm);
    } else decodeTerm(v);
  }
  // asserted: the decoder's result, checked field by field above
  return value as Term;
}

/* Readable notation for terms, as commit records and the lowering dump show
 * them. Each table is keyed by the constructors of `Term`, `Tag` and
 * `CallCode`: adding a constructor there and not here is a type error. */
type ObjectTerm = Exclude<Term, string>;
type Args<K extends TermKey> = Extract<ObjectTerm, Record<K, unknown>>[K];
const showTerms = (ts: Term[]): string => ts.map(showTerm).join(", ");
const SHOW_ATOM: Record<Extract<Term, string>, string> = { nul: "null", undef: "undefined", tru: "true", fls: "false" };
const SHOW_TERM: { [K in TermKey]: (a: Args<K>) => string } = {
  num: a => `num#${a.bits}`,
  str: a => JSON.stringify(a.value),
  bigint: a => `${a.value}n`,
  var: a => `x${a.i}`,
  invoke: a => `${showTerm(a.f)}.call(${[a.r, ...a.args].map(showTerm).join(", ")})`,
  letE: a => `let ${showTerm(a.a)} in ${showTerm(a.b)}`,
  objAt: a => `obj#${a.identity}{${a.fields.map(([k, l]) => `${k}: ℓ${l}`).join(", ")}}${showCode(a.call)}`,
  makeAt: a => `new{${a.names.map((n, i) => `${n}: ${a.inits[i] === undefined ? "?" : showTerm(a.inits[i])}`).join(", ")}}${showCode(a.call)}`,
  readAt: a => `${showTerm(a.a)}.${a.field}`,
  indexAt: a => `${showTerm(a.a)}[${showTerm(a.key)}]`,
  writeAt: a => `${showTerm(a.a)}.${a.field} := ${showTerm(a.b)}`,
  test: a => `${showTag(a.k)}(${showTerm(a.a)})`,
  ite: a => `if ${showTerm(a.c)} then ${showTerm(a.t)} else ${showTerm(a.e)}`,
  arith: a => `${showTerm(a.a)} ${a.op} ${showTerm(a.b)}`,
  arrLit: a => `[${showTerms(a.inits)}]`,
  elemAt: a => `${showTerm(a.a)}⟦${showTerm(a.i)}⟧`,
  setElem: a => `${showTerm(a.a)}⟦${showTerm(a.i)} ↦ ${showTerm(a.v)}⟧`,
  lenOf: a => `len(${showTerm(a.a)})`,
  arr: a => `store[${a.elems.map(e => (e === null ? "hole" : `ℓ${e}`)).join(", ")}]`,
  spread: a => `...${showTerm(a.a)}`,
  throw: a => `throw ${showTerm(a.a)}`,
  makeKey: a => `makeKey(${showTerm(a.key)}, ${showTerm(a.init)})`,
  merge: a => `merge(${showTerm(a.a)}, ${showTerm(a.b)}${a.drop.length ? ` drop ${a.drop.map(d => (typeof d === "string" ? d : `sym#${d.symbol}`)).join(", ")}` : ""})`,
};
/** A term in the notation of commit records. */
export function showTerm(t: Term): string {
  if (typeof t === "string") return SHOW_ATOM[t];
  const [k] = Object.keys(t);
  // asserted: a decoded term has exactly one constructor key, one of TermKey
  const show = SHOW_TERM[k as TermKey] as (a: unknown) => string;
  return show((t as Record<string, unknown>)[k]); // asserted: the constructor's own arguments
}
const SHOW_TAG: Record<Extract<Tag, string>, string> = {
  isNul: "isNull", isBool: "isBoolean", isRef: "isObject", isFun: "isFunction", isUndef: "isUndefined",
  isNullish: "isNullish", isNum: "isNumber", isStr: "isString", isBigint: "isBigInt", isSymbol: "isSymbol",
  truthy: "truthy", isArray: "Array.isArray", typeofObject: "typeofObject",
};
export function showTag(k: Tag): string {
  if (typeof k === "string") return SHOW_TAG[k];
  if ("hasKey" in k) return `has ${typeof k.hasKey.key === "string" ? k.hasKey.key : `sym#${k.hasKey.key.symbol}`}`;
  if ("numEq" in k) return `=== num#${k.numEq.bits}`;
  if ("strEq" in k) return `=== ${JSON.stringify(k.strEq.value)}`;
  if ("boolEq" in k) return `=== ${k.boolEq.value}`;
  return `=== ${k.bigintEq.value}n`;
}
function showCode(c: CallCode): string {
  if (c === "absent") return "";
  if ("closure" in c) return ` code(λ${c.closure.arity}. ${showTerm(c.closure.body)})`;
  if ("variadic" in c) return ` code(λ${c.variadic.fixed}+. ${showTerm(c.variadic.body)})`;
  if ("bound" in c) return ` code(bind ${showTerm(c.bound.target)})`;
  return ` code(graph of ${c.graph.exprs.length} nodes)`;
}
