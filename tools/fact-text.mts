// Facts of the verifier's heap knowledge (`HeapKnowledge.Knowledge` as JSON,
// tools/diagnostic.mts's `HeapKnowledge`), printed over source names: each
// slot named by a function the caller gives, from the point's bindings.
import { isJsonList, isJsonObject, type JsonRead, type JsonValue } from "./calculus.mts";
import type { HeapKnowledge, PropertyKey } from "./diagnostic.mts";

const num = (v: JsonRead): number => (typeof v === "number" ? v : -1);
const str = (v: JsonRead): string => (typeof v === "string" ? v : JSON.stringify(v ?? null) ?? "");
const list = (v: JsonRead): readonly JsonValue[] => (isJsonList(v) ? v : []);
const field = (v: JsonRead, k: string): JsonRead => (isJsonObject(v) ? v[k] : undefined);

/** A linear term: the slot's value, length, view length or string length,
 * read through its path of data fields, at the entry state (`old`) where it
 * is read there. */
function term(t: JsonRead, name: (slot: number) => string): string {
  const at = [name(num(field(t, "slot"))), ...list(field(t, "path")).map(str)].join(".");
  const kind = field(t, "kind");
  const read = kind === "value" ? at : kind === "length" ? `${at}.length` : `${str(kind)}(${at})`;
  return field(t, "atEntry") === true ? `old(${read})` : read;
}
/** An integer of a linear fact: a number, or the decimal digits of one past
 * the safe integers. */
const integer = (v: JsonRead): bigint => {
  if (typeof v === "string" && /^-?(0|[1-9][0-9]*)$/.test(v)) return BigInt(v);
  return BigInt(num(v));
};
/** Whether a term's text reads as one operand: a name, a path of names, or
 * a call of a name on one. */
const operand = (t: string): boolean => /^[A-Za-z_$%][\w$%@:]*(\.[A-Za-z_$][\w$]*)*$|^\w+\([^()]*\)$/.test(t);
/** A linear fact `Σ cᵢ·tᵢ op b`, each side a sum of positive multiples:
 * the terms of positive coefficient and `-b` where it is positive on the
 * left, the others on the right; a term named by a source expression in
 * parentheses. */
function sum(form: JsonRead, bound: JsonRead, op: string, name: (slot: number) => string): string {
  const left: string[] = [], right: string[] = [];
  // (a term named by a source expression, parenthesised)
  const multiple = (c: bigint, t: string): string => `${c === 1n ? "" : `${c}*`}${operand(t) ? t : `(${t})`}`;
  for (const p of list(form)) {
    const c = integer(isJsonList(p) ? p[1] : undefined);
    const t = term(isJsonList(p) ? p[0] : undefined, name);
    if (c > 0n) left.push(multiple(c, t));
    else if (c < 0n) right.push(multiple(-c, t));
  }
  const b = integer(bound);
  if (b < 0n) left.push(String(-b));
  else if (b > 0n || right.length === 0) right.push(String(b));
  return `${left.join(" + ") || "0"} ${op} ${right.join(" + ")}`;
}

/** An index fact over the point's binding names. */
export function indexFact(f: JsonRead, name: (slot: number) => string): string {
  const linear = field(field(f, "linear"), "fact");
  if (linear !== undefined) {
    const le = field(linear, "le"), ne = field(linear, "ne");
    if (le !== undefined) return sum(field(le, "form"), field(le, "bound"), "<=", name);
    return sum(field(ne, "form"), field(ne, "bound"), "!==", name);
  }
  const at = (k: string, s: string): string => name(num(field(field(f, k), s)));
  if (field(f, "int") !== undefined) return `safeInteger(${at("int", "slot")})`;
  if (field(f, "pastSafe") !== undefined) return `pastSafe(${at("pastSafe", "slot")})`;
  if (field(f, "index") !== undefined) return `index(${at("index", "slot")})`;
  if (field(f, "length") !== undefined) return `${at("length", "length")} === ${at("length", "array")}.length`;
  const bound = field(f, "bound");
  if (bound !== undefined)
    return `index(${at("bound", "index")}) && ${at("bound", "index")} ${field(bound, "strict") === true ? "<" : "<="} ${at("bound", "array")}.length`;
  const either = field(f, "either");
  if (either !== undefined)
    return `(${indexFact(field(either, "left"), name)}) || (${indexFact(field(either, "right"), name)})`;
  const guarded = field(f, "guarded");
  if (guarded !== undefined) {
    const at = [name(num(field(guarded, "slot"))), ...list(field(guarded, "path")).map(str)].join(".");
    return `${at} !== ${str(field(guarded, "tag"))} → ${indexFact(field(guarded, "body"), name)}`;
  }
  const element = field(f, "element");
  if (element !== undefined)
    return `${at("element", "value")} === ${at("element", "array")}[${at("element", "index")}]`;
  const apart = field(f, "apart");
  if (apart !== undefined) return `apart(${at("apart", "slot")}, ${at("apart", "other")})`;
  const spineApart = field(f, "spineApart");
  if (spineApart !== undefined) {
    const a = [at("spineApart", "slot"), ...list(field(spineApart, "path")).map(str)].join(".");
    const b = [at("spineApart", "other"), ...list(field(spineApart, "otherPath")).map(str)].join(".");
    return `apart(${a}, ${b})`;
  }
  const every = field(f, "every");
  if (every !== undefined) {
    const at = [name(num(field(every, "slot"))), ...list(field(every, "path")).map(str)].join(".");
    return `every element of ${at} below ${term(field(every, "stop"), name)}: ${JSON.stringify(field(every, "body"))}`;
  }
  return JSON.stringify(f ?? null) ?? "";
}

/** A property key: a string, or a well-known symbol by its number. */
const keyText = (k: PropertyKey): string => (typeof k === "string" ? k : `[Symbol ${k.symbol}]`);

/** A value set: the kinds it admits, with their literal lists. */
function contents(v: HeapKnowledge["cells"][number]["contents"]): string {
  const kinds: string[] = [];
  for (const k of ["nul", "undef", "tru", "fls", "sym", "arr"] as const) if (v[k]) kinds.push(k);
  for (const k of ["num", "str", "big"] as const) kinds.push(`${k}${JSON.stringify(v[k])}`);
  if (v.obj !== null) kinds.push(`obj${JSON.stringify(v.obj)}`);
  return kinds.join(" | ") || "nothing";
}

/** What a condition slot adds before a fact: `x → ` or `!x → `. */
function condition(f: { cond?: number; negated: boolean }, name: (slot: number) => string): string {
  return f.cond === undefined ? "" : `${f.negated ? "!" : ""}${name(f.cond)} → `;
}

/** Every fact of a knowledge, grouped by kind, each over source names. */
export function knowledgeFacts(k: HeapKnowledge, name: (slot: number) => string): { kind: string; text: string }[] {
  const out: { kind: string; text: string }[] = [];
  for (const c of k.cells) out.push({ kind: "cell", text: `${name(c.slot)}.${keyText(c.field)} : ${contents(c.contents)}` });
  for (const c of k.values)
    out.push({ kind: "value", text: `${name(c.slot)}${c.field === "" ? "" : "." + keyText(c.field)} : ${contents(c.contents)}` });
  for (const l of k.links) {
    const cell = name(l.cell), value = name(l.value);
    out.push({ kind: "link", text: l.alias ? `${value} === ${cell}` : `${value} === ${cell}${l.optional ? "?." : "."}${keyText(l.field)}` });
  }
  const depth = k.separation.depth;
  const level = (l: number): string => name(depth - 1 - l);
  const keys = (fs: readonly PropertyKey[] | null): string => (fs === null ? "" : `.{${fs.map(keyText).join(",")}}`);
  for (const s of k.separation.facts)
    out.push({ kind: "separation", text: `${level(s.slot)}${keys(s.fields)} apart from ` +
      s.partners.map(([p, fs]) => `${level(p)}${keys(fs)}`).join(", ") });
  for (const e of k.elems)
    out.push({ kind: "elements", text: `${condition(e, name)}every element of ${name(e.slot)} is ${e.pred.join(" | ")}` });
  for (const i of k.indices) {
    const f = i.fact;
    const kind = "linear" in f ? "linear" : "guarded" in f ? "guarded" : "either" in f ? "either" : "index";
    out.push({ kind, text: `${condition(i, name)}${indexFact(f, name)}` });
  }
  return out;
}
