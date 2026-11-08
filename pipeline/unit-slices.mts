// The units a document is proposed in, and each unit's slice: the document
// a unit's proposal and explanation read. The slices are inputs of stages,
// which key them by content; this module only computes them.

import { createHash } from "node:crypto";
import type { Json } from "../tools/calculus.mts";
import type { UnitFacts } from "./unit-documents.mts";
export type { UnitFacts };

type JsonRecord = { [key: string]: Json };
const isRecord = (value: Json | undefined): value is JsonRecord =>
  typeof value === "object" && value !== null && !Array.isArray(value);
const isList = (value: Json | undefined): value is Json[] => Array.isArray(value);
const listOf = (value: Json | undefined): Json[] => (isList(value) ? value : []);
const isSpan = (value: Json | undefined): value is [number, number] =>
  isList(value) && value.length === 2 && typeof value[0] === "number" && typeof value[1] === "number";

const strings = (value: Json | undefined, what: string): string[] => {
  if (!isList(value) || !value.every((s): s is string => typeof s === "string"))
    throw Error(`tool failure: producer --units printed ${what} without its names`);
  return value;
};
/** `producer --units`'s output, read field by field. */
export function decodeUnitFacts(value: Json): UnitFacts {
  if (!isRecord(value) || !isList(value.functions)) throw Error("tool failure: producer --units printed no functions");
  const functions = value.functions.map((f) => {
    if (!isRecord(f) || typeof f.name !== "string" || typeof f.init !== "boolean")
      throw Error("tool failure: producer --units printed a malformed function");
    return { name: f.name, mentions: strings(f.mentions, "a function"), init: f.init };
  });
  const init = value.init === null ? null
    : isRecord(value.init) ? { mentions: strings(value.init.mentions, "the initialization") }
    : null;
  if (value.init !== null && init === null) throw Error("tool failure: producer --units printed a malformed initialization");
  return { functions, init, readAsValues: strings(value.readAsValues, "the constants read as values") };
}

/** A unit of proposal: a strongly connected component of the graph of
 * mentions, the initialization a node of it; its members, whether the
 * initialization is one, whether its slice holds the initialization, and
 * the functions its slice holds by signature alone. */
export type ProposalUnit = { members: string[]; init: boolean; holdsInit: boolean; reads: string[] };

const initNode = "\u0000init";
/** The units of `facts`, each after the units it reads (Tarjan's order). */
export function proposalUnits(facts: UnitFacts): ProposalUnit[] {
  const edges = new Map<string, string[]>();
  for (const f of facts.functions) edges.set(f.name, [...f.mentions, ...(f.init && facts.init ? [initNode] : [])]);
  if (facts.init) edges.set(initNode, facts.init.mentions);
  const index = new Map<string, number>(), low = new Map<string, number>(), stack: string[] = [], on = new Set<string>();
  const components: string[][] = [];
  let next = 0;
  const visit = (v: string): void => {
    index.set(v, next);
    low.set(v, next);
    next++;
    stack.push(v);
    on.add(v);
    for (const w of edges.get(v) ?? []) {
      if (!edges.has(w)) continue;
      if (!index.has(w)) {
        visit(w);
        low.set(v, Math.min(low.get(v) ?? 0, low.get(w) ?? 0));
      } else if (on.has(w)) low.set(v, Math.min(low.get(v) ?? 0, index.get(w) ?? 0));
    }
    if (low.get(v) === index.get(v)) {
      const component: string[] = [];
      for (let w = stack.pop(); w !== undefined; w = stack.pop()) {
        on.delete(w);
        component.push(w);
        if (w === v) break;
      }
      components.push(component);
    }
  };
  for (const v of edges.keys()) if (!index.has(v)) visit(v);
  const order = [...edges.keys()];
  return components.map((component) => {
    const members = component.filter((v) => v !== initNode).sort((a, b) => order.indexOf(a) - order.indexOf(b));
    const init = component.includes(initNode);
    const holdsInit = init || members.some((m) => facts.functions.find((f) => f.name === m)?.init === true);
    const read = new Set<string>();
    for (const m of members) for (const n of facts.functions.find((f) => f.name === m)?.mentions ?? []) read.add(n);
    if (holdsInit) for (const n of facts.init?.mentions ?? []) read.add(n);
    return { members, init, holdsInit, reads: order.filter((n) => n !== initNode && read.has(n) && !members.includes(n)) };
  });
}

/** The extent of the positions a value holds: the least start and greatest
 * end of its spans, or null. */
function extent(value: Json): [number, number] | null {
  let from = Infinity, to = -Infinity;
  const walk = (v: Json): void => {
    // A declaration's identity is at its declaration, elsewhere.
    if (isRecord(v) && typeof v.module === "string") return;
    if (isRecord(v)) {
      for (const [k, x] of Object.entries(v)) {
        if ((k === "pos" || k === "span" || k === "namePos") && isSpan(x)) {
          from = Math.min(from, x[0]);
          to = Math.max(to, x[1]);
        } else walk(x);
      }
    } else if (isList(v)) v.forEach(walk);
  };
  walk(value);
  return from <= to ? [from, to] : null;
}

/** Each declaration of the document's own module by its canonical identity:
 * its name and its index among the declarations of that name, in source
 * order. A declaration inserted in one place renumbers only those of its
 * name. */
function localIdentities(document: JsonRecord, local: string): Map<string, number> {
  const spans = new Map<string, [number, number][]>();
  const walk = (v: Json): void => {
    if (isRecord(v)) {
      const span = v.span;
      if (typeof v.module === "string" && v.module.endsWith(local) && typeof v.name === "string" && isSpan(span)) {
        const key = `${v.module}#${v.name}`;
        const seen = spans.get(key) ?? [];
        if (!seen.some((s) => s[0] === span[0] && s[1] === span[1])) seen.push(span);
        spans.set(key, seen);
      }
      for (const x of Object.values(v)) walk(x);
    } else if (isList(v)) v.forEach(walk);
  };
  for (const [k, v] of Object.entries(document)) if (k !== "modules") walk(v);
  const ordinals = new Map<string, number>();
  for (const [name, list] of spans) {
    list.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    list.forEach((s, k) => ordinals.set(`${name}#${s[0]}:${s[1]}`, k));
  }
  return ordinals;
}

/** `text` with every number the groups of `pattern`'s matches capture
 * mapped by `at`. */
export function replaceNumbers(text: string, pattern: RegExp, at: (x: number) => number): string {
  let out = "", last = 0;
  for (const m of text.matchAll(new RegExp(pattern.source, "gd"))) {
    for (const [i, group] of m.slice(1).entries()) {
      const span = m.indices?.[i + 1];
      if (group === undefined || span === undefined) continue;
      out += text.slice(last, span[0]) + String(at(Number(group)));
      last = span[1];
    }
  }
  return out + text.slice(last);
}

/** The module every slice names the document's own declarations by. */
export const localModule = "local";

/** The document's positions at a slice that leaves out `deletions`, sorted
 * and disjoint, each at one point: a position after a deleted interval moves
 * back by its length, and one inside it moves to its start. */
export function toSlice(deletions: readonly (readonly [number, number])[], x: number): number {
  let removed = 0;
  for (const [s, e] of deletions) {
    if (x <= s) break;
    if (x < e) return s - removed;
    removed += e - s;
  }
  return x - removed;
}
/** A slice's position at the document: the inverse of `toSlice` outside the
 * deleted intervals (`to_document` of the producer). */
export function toDocument(deletions: readonly (readonly [number, number])[], y: number): number {
  let removed = 0;
  for (const [s, e] of deletions) {
    if (y <= s - removed) break;
    removed += e - s;
  }
  return y + removed;
}

/** The document with every position of its own code mapped by `at` and each
 * of its own declarations named canonically: a declaration of another module,
 * its definition and an imported value's type keep the coordinates of their
 * module. */
function mapped(local: string, at: (x: number) => number, ordinals: Map<string, number>): (v: Json) => Json {
  const identity = (v: JsonRecord): Json | null => {
    if (typeof v.module !== "string" || typeof v.name !== "string" || !isSpan(v.span)) return null;
    if (!v.module.endsWith(local)) return v;
    const k = ordinals.get(`${v.module}#${v.name}#${v.span[0]}:${v.span[1]}`);
    if (k === undefined) throw Error(`tool failure: a declaration ${v.name} of the document has no identity`);
    return { ...v, module: v.module.replaceAll(local, localModule), span: [0, k] };
  };
  const walk = (v: Json): Json => {
    if (isRecord(v)) {
      const named = identity(v);
      if (named !== null) return named;
      const out: JsonRecord = {};
      for (const [k, x] of Object.entries(v))
        out[k] = (k === "pos" || k === "span" || k === "namePos") && isSpan(x) ? [at(x[0]), at(x[1])]
          // A name the parser makes at a position, `…@N…`: no source name has `@`.
          : (k === "name" || k === "label") && typeof x === "string" && x.startsWith("%")
          ? replaceNumbers(x, /@(\d+)(?::(\d+))?/g, at)
          : walk(x);
      return out;
    }
    if (typeof v === "string" && v.includes(local)) return v.replaceAll(local, localModule);
    return isList(v) ? v.map(walk) : v;
  };
  return walk;
}
/** The declarations of a slice. The document's own are mapped by `walk`.
 * Another module's definition, and an imported value's type, hold spans of
 * that module and spans of the document's reads of its members alike: both
 * are erased (`erase`), each declaration's identity kept. */
function declarationsOf(declarations: Json, walk: (v: Json) => Json, erase: (v: Json) => Json, local: string): Json {
  if (!isRecord(declarations)) return walk(declarations);
  const own = (d: Json): boolean => isRecord(d) && isRecord(d.declaration) && typeof d.declaration.module === "string" &&
    d.declaration.module.endsWith(local);
  const out: JsonRecord = {};
  for (const [k, v] of Object.entries(declarations))
    out[k] = k === "definitions" ? listOf(v).map((d) => own(d) ? walk(d) : erase(d))
      : k === "values" ? listOf(v).map((d) => own(d) || !isRecord(d) ? walk(d)
        : { ...asRecord(erase(d)), binding: walk(d.binding ?? null) })
      : walk(v);
  return out;
}
const asRecord = (v: Json): JsonRecord => (isRecord(v) ? v : {});

/** A unit's slice: the document with the unit's members whole, each function
 * it reads by its signature (its body left out), the initialization where it
 * holds it, every other function and top-level statement left out, and its
 * own declarations named canonically; and the intervals left out. */
export function sliceOf(document: JsonRecord, local: string, unit: ProposalUnit):
    { text: string; deletions: [number, number][] } {
  const deletions: [number, number][] = [];
  const functions: JsonRecord[] = [];
  for (const f of listOf(document.functions)) {
    if (!isRecord(f) || typeof f.name !== "string") throw Error("tool failure: a function of the document has no name");
    if (unit.members.includes(f.name)) functions.push(f);
    else if (unit.reads.includes(f.name)) {
      // The body is left out from the end of the signature, so an edit
      // anywhere inside it, a comment before its first statement too, moves
      // nothing the slice holds.
      const stub = { ...f, body: [] };
      const body = extent(f.body ?? null), signature = extent(stub);
      if (body) deletions.push([signature ? Math.min(signature[1], body[0]) : body[0], body[1]]);
      functions.push(stub);
    } else {
      const whole = extent(f);
      if (whole) deletions.push(whole);
    }
  }
  const init = unit.holdsInit ? listOf(document.init) : [];
  if (!unit.holdsInit) for (const s of listOf(document.init)) {
    const whole = extent(s);
    if (whole) deletions.push(whole);
  }
  // An interval holding kept code is kept: a function nested in another, or
  // a class's member inside the initialization's statement.
  const kept = [...functions.map((f) => extent(f)), ...init.map((st) => extent(st))]
    .filter((e): e is [number, number] => e !== null);
  const deletable = deletions.filter((d) => !kept.some((k) => k[0] < d[1] && d[0] < k[1]));
  deletions.length = 0;
  deletions.push(...deletable);
  deletions.sort((a, b) => a[0] - b[0]);
  const merged: [number, number][] = [];
  for (const d of deletions) {
    const last = merged.at(-1);
    if (last && d[0] <= last[1]) last[1] = Math.max(last[1], d[1]);
    else merged.push([d[0], d[1]]);
  }
  const ordinals = localIdentities(document, local);
  const walk = mapped(local, (x) => toSlice(merged, x), ordinals), erase = mapped(local, () => 0, ordinals);
  const slice: JsonRecord = {};
  for (const [k, v] of Object.entries(document)) {
    if (k === "file") slice[k] = "unit.ts";
    else if (k === "sourceSha256") slice[k] = "";
        else if (k === "declarations") slice[k] = declarationsOf(v, walk, erase, local);
    else if (k === "functions") slice[k] = functions.map(walk);
    else if (k === "init") slice[k] = init.map(walk);
    // A slice's proposal reads no imported module's document.
    else if (k === "modules") slice[k] = [];
    else slice[k] = walk(v);
  }
  slice.sourceSha256 = createHash("sha256").update(JSON.stringify(slice)).digest("hex");
  return { text: JSON.stringify(slice), deletions: merged };
}

/** The document with its own declarations named as every slice names them:
 * what the assembly decodes the units' proposals against. */
export function canonicalDocument(document: JsonRecord, local: string): string {
  const walk = mapped(local, (x) => x, localIdentities(document, local));
  const out: JsonRecord = {};
  for (const [k, v] of Object.entries(document))
    out[k] = k === "modules" || k === "file" || k === "sourceSha256" ? v : walk(v);
  return JSON.stringify(out);
}
