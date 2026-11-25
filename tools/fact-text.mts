// Facts of the verifier's heap knowledge (tools/diagnostic.mts's decoded
// `HeapKnowledge`), printed over source names: each slot named by a function
// the caller gives, from the point's bindings.
import type { Tag } from "./calculus.mts";
import type {
  BodyFormula, BodyVariable, HeapKnowledge, IndexFact, Integer, LinearTerm, LitSet, PropertyKey, ValueSet,
} from "./diagnostic.mts";

/** A slot's name. */
type Namer = (slot: number) => string;

/** Whether a term's text reads as one operand: a name, a path of names, or
 * a call of a name on one. */
const operand = (t: string): boolean => /^[A-Za-z_$][\w$]*(\.[A-Za-z_$][\w$]*)*$|^\w+\([^()]*\)$/.test(t);
/** A term's text as one operand: in parentheses where it is a source
 * expression. */
const asOperand = (t: string): string => (operand(t) ? t : `(${t})`);

/** A path of data fields read from a slot. */
const pathText = (slot: number, path: readonly string[], name: Namer): string =>
  [asOperand(name(slot)), ...path].join(".");

function termKindText(kind: LinearTerm["kind"], at: string): string {
  if (typeof kind !== "string") return `(${at} & ${kind.bitMask.mask})`;
  return kind === "value" ? at : kind === "length" ? `${at}.length` : `${kind}(${at})`;
}

/** A linear term: the slot's value, length, view length, string length or
 * bitmask, read through its path of data fields, at the entry state (`old`)
 * where it is read there. */
function term(t: LinearTerm, name: Namer): string {
  const at = pathText(t.slot, t.path, name);
  const read = termKindText(t.kind, at);
  return t.atEntry === true ? `old(${read})` : read;
}

/** The largest safe integer, the bound a linear fact over one term states
 * `safeInteger` by (tools/bound-annotations.mts). */
const MAX_SAFE = 9007199254740991n;

/** A linear fact over variables printed by `text`: `safeInteger(t)` for
 * `t <= 2^53 - 1`; otherwise each side a sum of positive multiples, equal
 * variables merged, the terms of positive coefficient and `-b` where it is
 * positive on the left, the others on the right; null for one whose form
 * cancels and that holds (a tautology). */
function linear<V>(form: readonly (readonly [V, Integer])[], bound: Integer, ne: boolean, text: (v: V) => string): string | null {
  const merged = new Map<string, bigint>();
  for (const [v, c] of form) {
    const t = text(v);
    merged.set(t, (merged.get(t) ?? 0n) + BigInt(c));
  }
  const terms = [...merged].filter(([, c]) => c !== 0n);
  const b = BigInt(bound);
  if (terms.length === 0 && (ne ? b !== 0n : b >= 0n)) return null;
  const only = terms[0];
  if (!ne && terms.length === 1 && only !== undefined && only[1] === 1n && b === MAX_SAFE) return `safeInteger(${only[0]})`;
  const left: string[] = [], right: string[] = [];
  const multiple = (c: bigint, t: string): string => `${c === 1n ? "" : `${c}*`}${c === 1n ? t : asOperand(t)}`;
  for (const [t, c] of terms) {
    if (c > 0n) left.push(multiple(c, t));
    else right.push(multiple(-c, t));
  }
  if (b < 0n) left.push(String(-b));
  else if (b > 0n) right.push(String(b));
  return `${left.join(" + ") || "0"} ${ne ? "!==" : "<="} ${right.join(" + ") || "0"}`;
}

function shiftText(sh: { terms: [LinearTerm, Integer][]; offset: Integer }, base: string | null, name: Namer): string {
  const parts: string[] = base === null ? [] : [base];
  for (const [t, coeff] of sh.terms) {
    const c = BigInt(coeff);
    if (c === 0n) continue;
    const text = term(t, name);
    if (c === 1n) parts.push(parts.length === 0 ? text : `+ ${text}`);
    else if (c === -1n) parts.push(parts.length === 0 ? `-${text}` : `- ${text}`);
    else if (c > 0n) parts.push(parts.length === 0 ? `${c} * ${text}` : `+ ${c} * ${text}`);
    else parts.push(parts.length === 0 ? `-${-c} * ${text}` : `- ${-c} * ${text}`);
  }
  const off = BigInt(sh.offset);
  if (off > 0n) parts.push(parts.length === 0 ? String(off) : `+ ${off}`);
  else if (off < 0n) parts.push(parts.length === 0 ? String(off) : `- ${-off}`);
  return parts.join(" ") || "0";
}

/** A quantified fact's body variable: the index `k`, the element `e`, the
 * element at `k + d` of the array, a term over the element, or a term. */
function bodyVariable(v: BodyVariable, array: string, name: Namer): string {
  if (v === "index") return "k";
  if (v === "elem") return "e";
  if ("offset" in v) return `${array}[k + ${v.offset.delta}]`;
  if ("project" in v) {
    const at = ["e", ...v.project.path].join(".");
    return termKindText(v.project.kind, at);
  }
  if ("parallel" in v) {
    const arr = pathText(v.parallel.slot, v.parallel.path, name);
    const at = [`${arr}[${shiftText(v.parallel.shift, "k", name)}]`, ...v.parallel.elemPath].join(".");
    return termKindText(v.parallel.kind, at);
  }
  return term(v, name);
}
function body(f: BodyFormula, array: string, name: Namer): string {
  if ("guarded" in f) {
    const g = f.guarded;
    const tgt = "self" in g.target ? ["e", ...g.target.self.path].join(".")
      : [`${pathText(g.target.parallel.slot, g.target.parallel.path, name)}[${shiftText(g.target.parallel.shift, "k", name)}]`,
        ...g.target.parallel.elemPath].join(".");
    if (!("guarded" in g.body) && !("either" in g.body) && g.body.form.length === 0 && !g.body.ne &&
        (typeof g.body.bound === "number" ? g.body.bound < 0 : BigInt(g.body.bound) < 0n)) {
      const holds = g.tag === "notNull" ? "!== null" : g.tag === "notUndefined" ? "!== undefined"
        : g.tag === "notTrue" ? "!== true" : g.tag === "notFalse" ? "!== false" : `=== ${g.tag}`;
      return `${tgt} ${holds}`;
    }
    const cond = g.tag === "notNull" ? "=== null" : g.tag === "notUndefined" ? "=== undefined"
      : g.tag === "notTrue" ? "=== true" : g.tag === "notFalse" ? "=== false" : `!== ${g.tag}`;
    return `${tgt} ${cond} → ${body(g.body, array, name)}`;
  }
  if ("either" in f) return `(${body(f.either.left, array, name)}) || (${body(f.either.right, array, name)})`;
  return linear(f.form, f.bound, f.ne, (v) => bodyVariable(v, array, name)) ?? "true";
}

/** An index fact over the point's binding names; null for a tautology. */
export function indexFact(f: IndexFact, name: Namer): string | null {
  if ("linear" in f) {
    const F = f.linear.fact;
    return "le" in F ? linear(F.le.form, F.le.bound, false, (t) => term(t, name))
      : linear(F.ne.form, F.ne.bound, true, (t) => term(t, name));
  }
  if ("int" in f) return `safeInteger(${name(f.int.slot)})`;
  if ("pastSafe" in f) return `pastSafe(${name(f.pastSafe.slot)})`;
  if ("index" in f) return `index(${name(f.index.slot)})`;
  if ("length" in f) return `${name(f.length.length)} === ${asOperand(name(f.length.array))}.length`;
  if ("bound" in f)
    return `index(${name(f.bound.index)}) && ${name(f.bound.index)} ${f.bound.strict ? "<" : "<="} ${asOperand(name(f.bound.array))}.length`;
  if ("either" in f)
    return `(${indexFact(f.either.left, name) ?? "true"}) || (${indexFact(f.either.right, name) ?? "true"})`;
  if ("guarded" in f) {
    const g = f.guarded;
    const cond = g.tag === "notNull" ? "=== null" : g.tag === "notUndefined" ? "=== undefined"
      : g.tag === "notTrue" ? "=== true" : g.tag === "notFalse" ? "=== false" : `!== ${g.tag}`;
    return `${pathText(g.slot, g.path, name)} ${cond} → ${indexFact(g.body, name) ?? "true"}`;
  }
  if ("element" in f)
    return `${name(f.element.value)} === ${asOperand(name(f.element.array))}[${shiftText(f.element.index, null, name)}]`;
  if ("fieldRead" in f)
    return `${name(f.fieldRead.value)} === ${asOperand(name(f.fieldRead.object))}.${f.fieldRead.field}`;
  if ("apart" in f) {
    const a = f.apart;
    return `apart(${pathText(a.slot, a.path, name)}, ${pathText(a.other, a.otherPath, name)})`;
  }
  if ("same" in f) return `${name(f.same.slot)} === ${name(f.same.other)}`;
  if ("spineApart" in f) {
    const a = f.spineApart;
    return `apart(${pathText(a.slot, a.path, name)}, ${pathText(a.other, a.otherPath, name)})`;
  }
  if ("elemSpineApart" in f) {
    const a = f.elemSpineApart;
    return `elemSpineApart(${pathText(a.slot, a.path, name)}, ${pathText(a.other, a.otherPath, name)})`;
  }
  if ("atIndex" in f) {
    const e = f.atIndex;
    const array = pathText(e.slot, e.path, name);
    const elem = `${array}[${shiftText(e.index, null, name)}]`;
    const b = body(e.body, array, name);
    if (e.guard === null) return `at ${elem}: ${b}`;
    const cond = e.guard === "notNull" ? "=== null" : e.guard === "notUndefined" ? "=== undefined"
      : e.guard === "notTrue" ? "=== true" : e.guard === "notFalse" ? "=== false" : `!== ${e.guard}`;
    return `${elem} ${cond} → ${b}`;
  }
  const e = f.every;
  const array = pathText(e.slot, e.path, name);
  const boundText = (b: { base: LinearTerm | null; offset: Integer }): string => {
    const off = typeof b.offset === "number" ? b.offset : BigInt(b.offset);
    if (b.base === null) return String(b.offset);
    const base = term(b.base, name);
    if (off === 0 || off === 0n) return base;
    return off > 0 ? `${base} + ${off}` : `${base} - ${typeof off === "bigint" ? -off : -off}`;
  };
  const range = e.start.base === null && (e.start.offset === 0 || e.start.offset === "0")
    ? `k < ${boundText(e.stop)}`
    : `${boundText(e.start)} <= k < ${boundText(e.stop)}`;
  return `every element e at ${range} of ${array}: ${e.body.map((b) => body(b, array, name)).join(" && ")}`;
}

/** A property key: a string, or a well-known symbol by its number. */
const keyText = (k: PropertyKey): string => (typeof k === "string" ? k : `[Symbol ${k.symbol}]`);

/** A number's IEEE-754 bit pattern, as decimal digits, as the number. */
function double(bits: string): string {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  const x = view.getFloat64(0);
  return Object.is(x, -0) ? "-0" : String(x);
}

/** A set of literals of one kind: none, the kind, the kind but some, or
 * some. */
function literals<T>(kind: string, set: LitSet<T>, text: (x: T) => string): string | null {
  if ("these" in set) return set.these.length === 0 ? null : set.these.map(text).join(" | ");
  return set.allBut.length === 0 ? kind : `${kind} but ${set.allBut.map(text).join(", ")}`;
}

/** A tag test's text. */
function tagText(t: Tag): string {
  switch (t.kind) {
    case "hasKey": return `has ${typeof t.key === "string" ? JSON.stringify(t.key) : `[Symbol ${t.key.symbol}]`}`;
    case "numEq": return `=== ${double(t.bits)}`;
    case "strEq": return `=== ${JSON.stringify(t.value)}`;
    case "boolEq": return `=== ${t.value}`;
    case "bigintEq": return `=== ${t.value}n`;
    default: return t.kind;
  }
}

/** A value set in source terms: the kinds and literals it admits, an
 * object by the tag tests it meets (every clause, each by one of its tests);
 * one admitting every value of all its kinds but a few, as the value but
 * those. */
export function valueSet(v: ValueSet): string {
  const full = <T,>(set: LitSet<T>): boolean => "allBut" in set && set.allBut.length === 0;
  const none = <T,>(set: LitSet<T>): boolean => "these" in set && set.these.length === 0;
  const parts: [string, "all" | "none" | string][] = [
    ["null", v.nul ? "all" : "none"], ["undefined", v.undef ? "all" : "none"],
    ["boolean", v.tru && v.fls ? "all" : v.tru ? "true" : v.fls ? "false" : "none"],
    ["symbol", v.sym ? "all" : "none"], ["array", v.arr ? "all" : "none"],
    ["number", full(v.num) ? "all" : none(v.num) ? "none" : literals("number", v.num, double) ?? "none"],
    ["string", full(v.str) ? "all" : none(v.str) ? "none" : literals("string", v.str, (x) => JSON.stringify(x)) ?? "none"],
    ["bigint", full(v.big) ? "all" : none(v.big) ? "none" : literals("bigint", v.big, (x) => `${x}n`) ?? "none"],
    ["object", v.obj === null ? "none" : v.obj.length === 0 ? "all" : `object where ${v.obj.map((clause) => {
      const tests = clause.map((l) => `${l.answer ? "" : "!"}${tagText(l.tag)}`);
      return tests.length === 1 ? tests.join("") : `(${tests.join(" || ")})`;
    }).join(" && ")}`],
  ];
  const absent = parts.filter(([, p]) => p === "none").map(([k]) => k);
  if (absent.length > 0 && parts.every(([, p]) => p === "all" || p === "none") && absent.length * 2 < parts.length)
    return `any value but ${absent.join(" | ")}`;
  return parts.filter(([, p]) => p !== "none").map(([k, p]) => (p === "all" ? k : p)).join(" | ") || "nothing";
}

/** What a condition slot adds before a fact: `x → ` or `!x → `. */
function condition(f: { cond?: number; negated: boolean }, name: Namer): string {
  return f.cond === undefined ? "" : `${f.negated ? "!" : ""}${name(f.cond)} → `;
}

/** Every fact of a knowledge, grouped by kind, each over source names, but
 * a tautology. The field a variable's cell holds its value in, of a slot
 * `variable` states holds a variable's cell, is named by the variable's
 * binding. */
export function knowledgeFacts(k: HeapKnowledge, name: Namer, variable: (slot: number) => boolean = () => false):
    { kind: string; text: string }[] {
  const out: { kind: string; text: string }[] = [];
  const cellText = (slot: number, field: PropertyKey): string =>
    field === "value" && variable(slot) ? name(slot) : `${asOperand(name(slot))}.${keyText(field)}`;
  for (const c of k.cells) out.push({ kind: "cell", text: `${cellText(c.slot, c.field)} : ${valueSet(c.contents)}` });
  for (const c of k.values)
    out.push({ kind: "value", text: `${c.field === "" ? name(c.slot) : cellText(c.slot, c.field)} : ${valueSet(c.contents)}` });
  for (const l of k.links) {
    const cell = name(l.cell), value = name(l.value);
    out.push({ kind: "link", text: l.alias ? `${value} === ${cell}` : `${value} === ${asOperand(cell)}${l.optional ? "?." : "."}${keyText(l.field)}` });
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
    const text = indexFact(i.fact, name);
    if (text === null) continue;
    const f = i.fact;
    const kind = "linear" in f ? "linear" : "guarded" in f ? "guarded" : "either" in f ? "either" : "index";
    out.push({ kind, text: `${condition(i, name)}${text}` });
  }
  return out;
}
