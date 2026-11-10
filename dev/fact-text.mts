// Facts of the verifier's heap knowledge (`HeapKnowledge.Knowledge` as JSON,
// tools/diagnostic.mts's `HeapKnowledge`), printed over source names: each
// slot named by a function the caller gives, from the point's bindings.
import { isJsonList, isJsonObject, type JsonRead, type JsonValue } from "../tools/calculus.mts";

const num = (v: JsonRead): number => (typeof v === "number" ? v : -1);
const str = (v: JsonRead): string => (typeof v === "string" ? v : JSON.stringify(v ?? null));
const list = (v: JsonRead): readonly JsonValue[] => (isJsonList(v) ? v : []);
const field = (v: JsonRead, k: string): JsonRead => (isJsonObject(v) ? v[k] : undefined);

/** A linear term: the slot's value, length, view length or string length,
 * read through its path of data fields. */
function term(t: JsonRead, name: (slot: number) => string): string {
  const at = [name(num(field(t, "slot"))), ...list(field(t, "path")).map(str)].join(".");
  const kind = field(t, "kind");
  return kind === "value" ? at : kind === "length" ? `${at}.length` : `${str(kind)}(${at})`;
}
function sum(form: JsonRead, bound: JsonRead, op: string, name: (slot: number) => string): string {
  const parts = list(form).map((p) => {
    const c = num(isJsonList(p) ? p[1] : undefined);
    const t = term(isJsonList(p) ? p[0] : undefined, name);
    return `${c === 1 ? "" : c === -1 ? "-" : `${c}*`}${t}`;
  });
  return `${parts.join(" + ") || "0"} ${op} ${num(bound)}`;
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
    return `${at("bound", "index")} ${field(bound, "strict") === true ? "<" : "<="} ${at("bound", "array")}.length`;
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
  const storeApart = field(f, "storeApart");
  if (storeApart !== undefined) {
    const a = [at("storeApart", "slot"), ...list(field(storeApart, "path")).map(str)].join(".");
    const b = [at("storeApart", "other"), ...list(field(storeApart, "otherPath")).map(str)].join(".");
    return `apart(${a}, ${b})`;
  }
  const every = field(f, "every");
  if (every !== undefined) {
    const at = [name(num(field(every, "slot"))), ...list(field(every, "path")).map(str)].join(".");
    return `every element of ${at} below ${term(field(every, "stop"), name)}: ${JSON.stringify(field(every, "body"))}`;
  }
  return JSON.stringify(f ?? null);
}

/** A value set: the kinds it admits, with their literal lists. */
function contents(v: JsonRead): string {
  const kinds: string[] = [];
  for (const k of ["nul", "undef", "tru", "fls", "sym", "arr"]) if (field(v, k) === true) kinds.push(k);
  for (const k of ["num", "str", "big"]) {
    const s = field(v, k);
    if (s === null || s === undefined) continue;
    kinds.push(`${k}${JSON.stringify(s)}`);
  }
  const obj = field(v, "obj");
  if (obj !== null && obj !== undefined) kinds.push(`obj${JSON.stringify(obj)}`);
  return kinds.join(" | ") || "nothing";
}

/** What a condition slot adds before a fact: `x → ` or `!x → `. */
function condition(f: JsonRead, name: (slot: number) => string): string {
  const cond = field(f, "cond");
  if (typeof cond !== "number") return "";
  return `${field(f, "negated") === true ? "!" : ""}${name(cond)} → `;
}

/** Every fact of a knowledge, grouped by kind, each over source names. */
export function knowledgeFacts(k: JsonRead, name: (slot: number) => string): { kind: string; text: string }[] {
  const out: { kind: string; text: string }[] = [];
  for (const c of list(field(k, "cells")))
    out.push({ kind: "cell", text: `${name(num(field(c, "slot")))}.${str(field(c, "field"))} : ${contents(field(c, "contents"))}` });
  for (const c of list(field(k, "values")))
    out.push({ kind: "value", text: `${name(num(field(c, "slot")))}${field(c, "field") === "" ? "" : "." + str(field(c, "field"))} : ${contents(field(c, "contents"))}` });
  for (const l of list(field(k, "links"))) {
    const cell = name(num(field(l, "cell"))), value = name(num(field(l, "value")));
    out.push({ kind: "link", text: field(l, "alias") === true ? `${value} === ${cell}`
      : `${value} === ${cell}${field(l, "optional") === true ? "?." : "."}${str(field(l, "field"))}` });
  }
  const separation = field(k, "separation");
  const depth = num(field(separation, "depth"));
  const level = (l: number): string => name(depth - 1 - l);
  const keys = (fs: JsonRead): string => (fs === null ? "" : `.{${list(fs).map(str).join(",")}}`);
  for (const s of list(field(separation, "facts")))
    out.push({ kind: "separation", text: `${level(num(field(s, "slot")))}${keys(field(s, "fields"))} apart from ` +
      list(field(s, "partners")).map((p) => isJsonList(p) ? `${level(num(p[0]))}${keys(p[1])}` : "?").join(", ") });
  for (const e of list(field(k, "elems")))
    out.push({ kind: "elements", text: `${condition(e, name)}elements of ${name(num(field(e, "slot")))} : ${list(field(e, "pred")).map(str).join(" | ")}` });
  for (const i of list(field(k, "indices"))) {
    const f = field(i, "fact");
    const kind = field(field(f, "linear"), "fact") !== undefined ? "linear" :
      field(f, "guarded") !== undefined ? "guarded" : field(f, "either") !== undefined ? "either" : "index";
    out.push({ kind, text: `${condition(i, name)}${indexFact(f, name)}` });
  }
  return out;
}
