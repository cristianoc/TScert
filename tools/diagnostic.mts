import { decodeGraph, decodeLabels, type Labels } from "./type-graph.mts";
// calculus.mts decodes the native terms a record's judgements and source map name.
// control-flow.mts decodes the program-graph node a node or edge obligation names.
import { decodeTag, decodeTerm, hasExactly, isParsedObject, nat, type Json, type Tag, type Term } from "./calculus.mts";
import { decodeNode, type ProgramNode } from "./control-flow.mts";
import type { Span } from "./span.mts";
import { illFormedString } from "./wire-strings.mts";
import { passToolFailure } from "./thrown.mts";

// Optional explanatory metadata, never evidence. A record this reader cannot
// decode field by field is left in the human diagnostic; it must not change the
// verification outcome.

/** Where the verifier stopped. */
type Phase = "proof-search" | "certificate-check" | "request-validation";

/**
 * Where a node the failure names sits, in the source the request came from.
 * Absent when the request carried no source map.
 */
export interface SourceMapEntry {
  pos: Span;
  role: string;
  environmentStart: number | null;
  context: {name: string; span: Span | null}[];
}

/** The judgement a failure could not establish. */
interface Sequent {
  context: Labels[];
  term: Term;
  type: Labels;
}

/** A set of literals: these, or every literal but these. */
type LitSet<T> = { these: T[] } | { allBut: T[] };
/** What a fact states of a runtime slot (for a cell, of the named field of
 * the object it holds; for a value, of the slot itself): a set of values, one
 * component per kind of value; an object is in it when it meets one of the
 * `obj` clauses, each a list of tag answers, or any object where `obj` is
 * null and none where it is empty. */
interface ValueSet {
  nul: boolean; undef: boolean; tru: boolean; fls: boolean; sym: boolean; arr: boolean;
  /** Numbers by their IEEE-754 bit patterns, as decimal digits. */
  num: LitSet<string>; str: LitSet<string>; big: LitSet<number>;
  obj: { tag: Tag; answer: boolean }[][] | null;
}
function litSet<T>(v: Json | undefined, item: (x: Json) => T): LitSet<T> {
  const r = isParsedObject(v) && "these" in v ? record(v,["these"]).these : record(v,["allBut"]).allBut;
  const xs = record(r,["xs"]).xs;
  if (!Array.isArray(xs)) throw Error("invalid literal set");
  const items = xs.map(item);
  return isParsedObject(v) && "these" in v ? { these: items } : { allBut: items };
}
function valueSet(v: Json): ValueSet {
  const f = record(v,["nul","undef","tru","fls","sym","arr","num","str","big","obj"]);
  const flag = (x: Json | undefined): boolean => {
    if (typeof x !== "boolean") throw Error("invalid value set flag");
    return x;
  };
  const number = (x: Json): number => {
    if (typeof x !== "number") throw Error("invalid value set number");
    return x;
  };
  const bits = (x: Json): string => {
    if (typeof x !== "string" || !/^(0|[1-9][0-9]*)$/.test(x)) throw Error("invalid value set number");
    return x;
  };
  const text = (x: Json): string => {
    if (typeof x !== "string") throw Error("invalid value set string");
    return x;
  };
  let obj: ValueSet["obj"] = null;
  if (f.obj !== null) {
    if (!Array.isArray(f.obj)) throw Error("invalid value set objects");
    obj = f.obj.map((clause) => {
      if (!Array.isArray(clause)) throw Error("invalid value set clause");
      return clause.map((literal) => {
        const l = record(literal,["tag","answer"]);
        if (typeof l.answer !== "boolean") throw Error("invalid tag answer");
        return { tag: decodeTag(l.tag), answer: l.answer };
      });
    });
  }
  return { nul: flag(f.nul), undef: flag(f.undef), tru: flag(f.tru), fls: flag(f.fls), sym: flag(f.sym), arr: flag(f.arr),
    num: litSet(f.num, bits), str: litSet(f.str, text), big: litSet(f.big, number), obj };
}
interface HeapFact {
  slot: number;
  contents: ValueSet;
  field: string;
}
export interface HeapKnowledge {
  cells: HeapFact[]; values: HeapFact[];
  /** A read link (`alias` false) or a value equality (`alias` true). A read
   * link through an `optional` key also covers the object lacking the key,
   * where the read gave `undefined`. */
  links: {cell: number; value: number; alias: boolean; field: string; optional: boolean}[];
  /** Which locations differ: facts addressed by level, level `l` naming slot
   * `depth - 1 - l`; a fact's subject `fields` (null: every own location)
   * differ from each partner's listed fields, each a property key: a
   * string, or a well-known symbol by its number. */
  separation: {depth: number; facts: {slot: number; fields: SeparationKey[] | null; partners: [number, SeparationKey[]][]}[]};
  /** Elements facts: every present element of the array slot `slot` holds is
   * of a kind `pred` lists, where the slot `cond`, if stated, holds a truthy
   * value, or a falsy one where `negated`. */
  elems: {slot: number; pred: ElemKind[]; cond?: number; negated: boolean}[];
  /** Index facts: the slot `k` holds an array index (`index`), the slot `n`
   * the length of the array slot `x`'s store (`length`), or `k` an index at
   * most that length (`bound`), where the slot `cond`, if stated, holds a
   * truthy value, or a falsy one where `negated`. */
  indices: {fact: IndexFact; cond?: number; negated: boolean}[];
}
type IndexFact = { index: { slot: number } } | { length: { array: number; length: number } } |
  { bound: { array: number; index: number; strict: boolean } } | { int: { slot: number } } |
  { pastSafe: { slot: number } } |
  { linear: { fact: { le: { form: [LinearTerm, number][]; bound: number } } | { ne: { form: [LinearTerm, number][]; bound: number } } } } |
  { either: { left: IndexFact; right: IndexFact } } |
  { guarded: { slot: number; path: string[]; tag: "null" | "undefined" | "true" | "false"; body: IndexFact } } |
  { element: { value: number; array: number; index: number } } |
  { every: { slot: number; path: string[]; stop: LinearTerm; body: BodyFormula[] } } |
  { apart: { slot: number; other: number } } |
  { storeApart: { slot: number; path: string[]; other: number; otherPath: string[] } };
/** A variable of a quantified fact's body: the index, the element, or a term. */
type BodyFormula = { form: [BodyVariable, number][]; bound: number; ne: boolean } |
  { either: { left: BodyFormula; right: BodyFormula } };
type BodyVariable = "index" | "elem" | { offset: { delta: number } } | LinearTerm | { project: LinearTerm };
/** A linear fact's term: a root slot, the named data fields read from it
 * (`path`), and what it reads of the value they end at: the value, the length
 * of its array store, or the length of its typed array. */
type LinearTerm = { kind: "value" | "length" | "view" | "strLength"; slot: number; path: string[] };
type SeparationKey = string | { symbol: number };
/** The value kinds an elements fact's predicate names. */
const ELEM_KINDS = ["nul", "undef", "bool", "num", "str", "big", "sym", "obj"] as const;
type ElemKind = (typeof ELEM_KINDS)[number];

/** A node of the certificate graph, as the failure reports it. */
interface DiagnosticNode {
  label: number;
  sourceMap: SourceMapEntry | null;
  node: ProgramNode | null;
  claim: { context: Labels[]; type: Labels } | null;
  requiredKnowledge: HeapKnowledge | null;
}

/**
 * What an edge carries from its source to its destination, mirroring the
 * continuation the source node ends in (RequestJson.lean, `failureDiagnostic`).
 */
interface DiagnosticTransfer {
  available: Labels[];
  target: { label: number; mapping: number[] | null };
  /** Which way a two-armed Boolean test went; null for every other edge. */
  booleanObservation: boolean | null;
  /** The tag test an edge answers, where the continuation is one. */
  tagObservation: { test: Tag; answer: boolean; slot: number } | null;
}

export type DiagnosticOutcome =
  | { kind: "not-established" }
  | { kind: "exhausted"; resource: {
      kind: "subtype-frontier"; limit: number; rounds: number; visited: number;
    } };

function diagnosticOutcome(value: Json | undefined): DiagnosticOutcome {
  if (!isParsedObject(value)) throw Error("invalid diagnostic outcome");
  switch (value.kind) {
    case "not-established": record(value, ["kind"]); return { kind: "not-established" };
    case "exhausted": {
      const outcome = record(value, ["kind", "resource"]);
      const resource = record(outcome.resource, ["kind", "limit", "rounds", "visited"]);
      if (resource.kind !== "subtype-frontier") throw Error("unknown search resource");
      const limit = nat(resource.limit), rounds = nat(resource.rounds), visited = nat(resource.visited);
      if (rounds > limit) throw Error("resource counts exceed budget");
      return { kind: "exhausted", resource: { kind: "subtype-frontier", limit, rounds, visited } };
    }
    default: throw Error("unknown diagnostic outcome");
  }
}

/** A fact the producer supplied at a statement entry that the search left
 * out: the entry, the node whose edge into it does not establish the fact
 * (the entry itself at the graph's entry), and the fact over the entry's
 * slots. */
export interface LeftOutCandidate {
  label: number;
  sourceMap: SourceMapEntry | null;
  edgeFrom: number;
  edgeSourceMap: SourceMapEntry | null;
  fact: HeapKnowledge["indices"][number];
}

/** What every record carries, whatever the failure was. */
interface Common {
  phase: Phase;
  outcome: DiagnosticOutcome;
  /** The proof budget the search was given. */
  fuel: number;
  /** The store's labels the record mentions, projected onto a finite table:
   * the document's rows, which `decodeGraph` checks. */
  types: Json;
  /**
   * A source-like spelling of each row of `types` that stands for an
   * application, `Promise<number | R>`, by row, in row order. Such a label is
   * shown by its name; a named row with no clauses is past the projection's
   * depth bound, an opaque reference. Absent when no row is named.
   */
  names?: [number, string][];
  /**
   * The result type the request asked for. Absent from a closure expression
   * claim, which is produced without a request and so has none — not an
   * omission to paper over.
   */
  requiredResult?: Labels;
  /** The facts the producer supplied at statement entries that the evidence
   * search of the refused graph left out. Absent from a record no graph
   * search makes. */
  candidatesLeftOut?: LeftOutCandidate[];
  /** Attached by the report writer, not by the verifier. */
  input?: {
    file: string;
    functionName: string;
    namePos: Span;
    sourceSha256: string;
    claimsSha256: string;
  };
}

/** A node of the certificate graph could not be typed. */
interface NodeTyping extends Common {
  kind: "node-typing";
  id: string;
  source: DiagnosticNode;
  sequent: Sequent;
}

/** An edge's destination was not justified by what its source carries. */
interface EdgeCoverage extends Common {
  kind: "edge-coverage";
  id: string;
  edgeIndex: number;
  source: DiagnosticNode;
  destination: DiagnosticNode;
  transfer: DiagnosticTransfer;
}

/**
 * A closure expression claim did not follow. This failure is raised where the
 * claim is rather than at a graph node, so it names its place directly instead
 * of hanging a source map under a node: see `sourceMap` above, and
 * ExpressionClaims.lean beside `failureDiagnostic` in RequestJson.lean.
 */
interface ExpressionClaimFailure extends Common {
  kind: "expression-claim";
  id: string;
  sourceMap: SourceMapEntry;
  sequent: Sequent;
}

/** `actual ≤ expected` between two ground types at a source span: a call of
 * a generic module value names its instance, and each type argument must lie
 * within its binder's bound. */
interface DirectJudgment {
  kind: "subtyping";
  subject: Span;
  actual: Labels;
  expected: Labels;
}

/** A check stopped on a judgment that is not an ordinary graph sequent: a
 * generic value's instance outside its bound. Its source place is mandatory. */
interface DirectObligationFailure extends Common {
  kind: "direct-obligation";
  id: string;
  sourceMap: SourceMapEntry;
  judgment: DirectJudgment;
}

/** Source conversion stopped before a semantic judgment existed. This is a
 * located refusal, never a sequent and never a failed proof. */
interface SourceRefusal extends Common {
  kind: "source-refusal";
  id: string;
  sourceMap: SourceMapEntry;
  reason: string;
}

/** Something was produced and then rejected by the independent check. */
interface ProductionFailure extends Common {
  kind: "production-failure";
  failure: string;
}

export type ObligationDiagnostic =
  | NodeTyping
  | EdgeCoverage
  | ExpressionClaimFailure
  | DirectObligationFailure
  | SourceRefusal
  | ProductionFailure;

const PHASES: readonly (Json | undefined)[] = [
  "proof-search",
  "certificate-check",
  "request-validation",
];
/** Each kind's own fields, keyed by `ObligationDiagnostic`'s kinds: a key
 * outside the union fails to compile, and tests/diagnostic.mts decodes a
 * record of every kind of the union. */
const KIND_FIELDS: readonly (readonly [ObligationDiagnostic["kind"], readonly string[]])[] = [
  ["node-typing", ["id", "source", "sequent"]],
  ["edge-coverage", ["id", "edgeIndex", "source", "destination", "transfer"]],
  ["expression-claim", ["id", "sourceMap", "sequent"]],
  ["direct-obligation", ["id", "sourceMap", "judgment"]],
  ["source-refusal", ["id", "sourceMap", "reason"]],
  ["production-failure", ["failure"]],
];
const PREFIX = "obligation-diagnostic: ";

/** A parsed object: the record is read from `JSON.parse`'s data. */
type Fields = { [key: string]: Json };
function record(v: Json | undefined, required: string[], optional: string[] = []): Fields {
  if (!isParsedObject(v) || !hasExactly(v, required, optional)) throw Error("invalid diagnostic fields");
  return v;
}
function span(v: Json | undefined): Span {
  if (!Array.isArray(v) || v.length !== 2) throw Error("invalid diagnostic span");
  const start = nat(v[0]), end = nat(v[1]);
  if (end < start) throw Error("reversed span");
  return [start, end];
}

function sourceMap(v: Json | undefined): SourceMapEntry | null {
  if (v === null) return null;
  const m = record(v,["pos","role","environmentStart","context"]);
  const pos = span(m.pos);
  const role = m.role;
  if (typeof role !== "string") throw Error("invalid role");
  const environmentStart = m.environmentStart === null ? null : nat(m.environmentStart);
  if (!Array.isArray(m.context)) throw Error("invalid source context");
  const context: SourceMapEntry["context"] = [];
  for (const entry of m.context) {
    const d = record(entry,["name","span"]);
    const name = d.name;
    if (typeof name !== "string") throw Error("invalid binding name");
    const at = d.span === null ? null : span(d.span);
    context.push({ name, span: at });
  }
  return { pos, role, environmentStart, context };
}

function directJudgment(v: Json | undefined, size: number): DirectJudgment {
  const j = record(v,["kind","subject","actual","expected"]);
  if (j.kind !== "subtyping") throw Error("unknown direct-obligation judgment");
  const subject = span(j.subject);
  return {kind:"subtyping",subject,
    actual:decodeLabels(j.actual,size),expected:decodeLabels(j.expected,size)};
}
function knowledge(v: Json | undefined): HeapKnowledge | null {
  if (v === null) return null;
  const k = record(v,["cells","values","links","separation","elems","indices"]);
  const factsOf = (facts: Json | undefined): HeapFact[] => {
    if (!Array.isArray(facts)) throw Error("invalid heap facts");
    const result: HeapFact[] = [];
    for (const fact of facts) {
      const f = record(fact,["slot","contents","field"]); const slot = nat(f.slot);
      const field = f.field;
      if (typeof field !== "string") throw Error("invalid heap fact field");
      result.push({ slot, field, contents: valueSet(f.contents) });
    }
    return result;
  };
  const cells = factsOf(k.cells), values = factsOf(k.values);
  if (!Array.isArray(k.links)) throw Error("invalid heap links");
  const links: HeapKnowledge["links"] = [];
  for (const link of k.links) {
    const l = record(link,["cell","value","alias","field","optional"]);
    const cell = nat(l.cell), value = nat(l.value);
    if (typeof l.optional !== "boolean") throw Error("invalid optional flag");
    if (typeof l.field !== "string") throw Error("invalid heap link field");
    if (typeof l.alias !== "boolean") throw Error("invalid alias");
    links.push({ cell, value, optional: l.optional, field: l.field, alias: l.alias });
  }
  const keys = (v: Json | undefined): SeparationKey[] => {
    if (!Array.isArray(v)) throw Error("invalid separation fields");
    const result: SeparationKey[] = [];
    for (const f of v) {
      if (typeof f === "string") result.push(f);
      else result.push({ symbol: nat(record(f,["symbol"]).symbol) });
    }
    return result;
  };
  const s = record(k.separation,["depth","facts"]); const depth = nat(s.depth);
  if (!Array.isArray(s.facts)) throw Error("invalid separation facts");
  const facts: HeapKnowledge["separation"]["facts"] = [];
  for (const fact of s.facts) {
    const f = record(fact,["slot","fields","partners"]); const slot = nat(f.slot);
    const fields = f.fields === null ? null : keys(f.fields);
    if (!Array.isArray(f.partners)) throw Error("invalid separation partners");
    const partners: [number, SeparationKey[]][] = [];
    for (const p of f.partners) {
      if (!Array.isArray(p) || p.length !== 2) throw Error("invalid separation partner");
      partners.push([nat(p[0]), keys(p[1])]);
    }
    facts.push({ slot, fields, partners });
  }
  if (!Array.isArray(k.elems)) throw Error("invalid elements facts");
  const elems: HeapKnowledge["elems"] = [];
  for (const atom of k.elems) {
    const a = record(atom,["slot","pred","negated"],["cond"]);
    const p = record(a.pred,[...ELEM_KINDS]);
    if (typeof a.negated !== "boolean") throw Error("invalid elements fact");
    const pred: ElemKind[] = [];
    for (const kind of ELEM_KINDS) {
      const holds = p[kind];
      if (typeof holds !== "boolean") throw Error("invalid elements predicate");
      if (holds) pred.push(kind);
    }
    elems.push({ slot: nat(a.slot), pred, negated: a.negated, ...(a.cond === undefined ? {} : { cond: nat(a.cond) }) });
  }
  if (!Array.isArray(k.indices)) throw Error("invalid index facts");
  const indices: HeapKnowledge["indices"] = [];
  for (const atom of k.indices) indices.push(indexAtom(atom));
  return { cells, values, links, separation: { depth, facts }, elems, indices };
}

/** An index atom (`HeapKnowledge.IndexAtom`): its fact, and the guard it
 * holds under where it has one. */
function indexAtom(atom: Json | undefined): HeapKnowledge["indices"][number] {
  const a = record(atom,["fact","cond","negated"]);
  if (typeof a.negated !== "boolean") throw Error("invalid index fact");
  const fact = indexFact(a.fact);
  return { fact, negated: a.negated, ...(a.cond === null ? {} : { cond: nat(a.cond) }) };
}

/** The candidates the search left out (RequestJson.lean, `failureDiagnostic`). */
function leftOut(v: Json | undefined): LeftOutCandidate[] {
  if (!Array.isArray(v)) throw Error("invalid candidates left out");
  return v.map((entry) => {
    const d = record(entry,["label","sourceMap","edgeFrom","edgeSourceMap","fact"]);
    return { label: nat(d.label), sourceMap: sourceMap(d.sourceMap), edgeFrom: nat(d.edgeFrom),
      edgeSourceMap: sourceMap(d.edgeSourceMap), fact: indexAtom(d.fact) };
  });
}

/** An index fact of a knowledge (`HeapKnowledge.IndexFact`), decoded field
 * by field; a guarded fact's body in turn. */
function indexFact(f: Json | undefined): IndexFact {
  if (f === null || typeof f !== "object" || Array.isArray(f)) throw Error("invalid index fact");
  let fact: IndexFact;
  if ("either" in f) {
    const e = record(record(f,["either"]).either,["left","right"]);
    return { either: { left: indexFact(e.left), right: indexFact(e.right) } };
  }
  if ("guarded" in f) {
    const g = record(record(f,["guarded"]).guarded,["slot","path","tag","body"]);
    const path = g.path;
    if (!Array.isArray(path) || !path.every((x: Json) => typeof x === "string")) throw Error("a guard's path");
    if (g.tag !== "null" && g.tag !== "undefined" && g.tag !== "true" && g.tag !== "false") throw Error("a guard's tag");
    return { guarded: { slot: nat(g.slot), path: path.filter((x: Json): x is string => typeof x === "string"), tag: g.tag,
      body: indexFact(g.body) } };
  }
  if ("apart" in f) {
    const r = record(record(f,["apart"]).apart,["slot","other"]);
    return { apart: { slot: nat(r.slot), other: nat(r.other) } };
  }
  if ("storeApart" in f) {
    const r = record(record(f,["storeApart"]).storeApart,["slot","path","other","otherPath"]);
    const fields = (p: Json): string[] => {
      if (!Array.isArray(p) || !p.every((x: Json) => typeof x === "string")) throw Error("a store separation's path");
      return p.filter((x: Json): x is string => typeof x === "string");
    };
    return { storeApart: { slot: nat(r.slot), path: fields(r.path), other: nat(r.other), otherPath: fields(r.otherPath) } };
  }
  if ("element" in f) {
    const e = record(record(f,["element"]).element,["value","array","index"]);
    return { element: { value: nat(e.value), array: nat(e.array), index: nat(e.index) } };
  }
  if ("every" in f) {
    const e = record(record(f,["every"]).every,["slot","path","stop","body"]);
    const path = e.path;
    if (!Array.isArray(path) || !path.every((x: Json) => typeof x === "string")) throw Error("a quantified fact's path");
    if (!Array.isArray(e.body)) throw Error("a quantified fact's body");
    const bodyFormula = (b: Json): BodyFormula => {
      if (typeof b === "object" && b !== null && !Array.isArray(b) && "either" in b) {
        const e = record(record(b,["either"]).either,["left","right"]);
        return { either: { left: bodyFormula(e.left), right: bodyFormula(e.right) } };
      }
      const { form, bound, ne } = linearForm<BodyVariable>(b, (x) => {
        if (x === "index" || x === "elem") return x;
        if (typeof x === "object" && x !== null && !Array.isArray(x) && "offset" in x) return { offset: { delta: nat(record(record(x,["offset"]).offset,["delta"]).delta) } };
        if (typeof x === "object" && x !== null && !Array.isArray(x) && "project" in x) {
          const p = record(record(x,["project"]).project,["kind","path"]);
          return { project: linearTerm({ kind: p.kind, path: p.path, slot: 0 }) };
        }
        return linearTerm(record(record(x,["free"]).free,["t"]).t);
      });
      return { form, bound, ne };
    };
    const body = e.body.map(bodyFormula);
    return { every: { slot: nat(e.slot), path: path.filter((x: Json): x is string => typeof x === "string"),
      stop: linearTerm(e.stop), body } };
  }
  if ("index" in f) fact = { index: { slot: nat(record(record(f,["index"]).index,["slot"]).slot) } };
  else if ("length" in f) {
    const l = record(record(f,["length"]).length,["array","length"]);
    fact = { length: { array: nat(l.array), length: nat(l.length) } };
  } else if ("bound" in f) {
    const b = record(record(f,["bound"]).bound,["array","index","strict"]);
    if (typeof b.strict !== "boolean") throw Error("a bound's strict is a Boolean");
    fact = { bound: { array: nat(b.array), index: nat(b.index), strict: b.strict } };
  } else if ("int" in f) {
    fact = { int: { slot: nat(record(record(f,["int"]).int,["slot"]).slot) } };
  } else if ("pastSafe" in f) {
    fact = { pastSafe: { slot: nat(record(record(f,["pastSafe"]).pastSafe,["slot"]).slot) } };
  } else {
    const stated = record(record(f,["linear"]).linear,["fact"]).fact;
    const le = isParsedObject(stated) && "le" in stated;
    const F = record(stated, le ? ["le"] : ["ne"]);
    const body = record(le ? F.le : F.ne, ["form","bound"]);
    if (!Array.isArray(body.form) || typeof body.bound !== "number") throw Error("a linear fact's form and bound");
    const form: [LinearTerm, number][] = body.form.map((t: Json): [LinearTerm, number] => {
      if (!Array.isArray(t) || t.length !== 2 || typeof t[1] !== "number") throw Error("a linear fact's term");
      const term = record(t[0], ["kind", "slot", "path"]);
      const kind = term.kind;
      if (kind !== "value" && kind !== "length" && kind !== "view" && kind !== "strLength") throw Error("a linear term's kind");
      const path = term.path;
      if (!Array.isArray(path) || !path.every((f: Json) => typeof f === "string")) throw Error("a linear term's path");
      return [{ kind, slot: nat(term.slot), path: path.filter((f: Json): f is string => typeof f === "string") }, t[1]];
    });
    fact = { linear: { fact: le ? { le: { form, bound: body.bound } } : { ne: { form, bound: body.bound } } } };
  }
  return fact;
}

/** A linear term of a knowledge, decoded field by field. */
function linearTerm(t: Json | undefined): LinearTerm {
  const term = record(t, ["kind", "slot", "path"]);
  const kind = term.kind;
  if (kind !== "value" && kind !== "length" && kind !== "view" && kind !== "strLength") throw Error("a linear term's kind");
  const path = term.path;
  if (!Array.isArray(path) || !path.every((f: Json) => typeof f === "string")) throw Error("a linear term's path");
  return { kind, slot: nat(term.slot), path: path.filter((f: Json): f is string => typeof f === "string") };
}

/** A linear fact over variables `variable` decodes: its form, its bound, and
 * whether it is `≠`. */
function linearForm<V>(stated: Json | undefined, variable: (x: Json | undefined) => V):
    { form: [V, number][]; bound: number; ne: boolean } {
  const le = isParsedObject(stated) && "le" in stated;
  const F = record(stated, le ? ["le"] : ["ne"]);
  const body = record(le ? F.le : F.ne, ["form","bound"]);
  if (!Array.isArray(body.form) || typeof body.bound !== "number") throw Error("a linear fact's form and bound");
  const form = body.form.map((t: Json): [V, number] => {
    if (!Array.isArray(t) || t.length !== 2 || typeof t[1] !== "number") throw Error("a linear fact's term");
    return [variable(t[0]), t[1]];
  });
  return { form, bound: body.bound, ne: !le };
}

/** A node record with its node decoded in place of its wire form, as the
 * term and tag below are. */
function diagnosticNode(v: Json | undefined, size: number): DiagnosticNode {
  const n = record(v,["label","sourceMap","node","claim","requiredKnowledge"]);
  const label = nat(n.label), map = sourceMap(n.sourceMap), requiredKnowledge = knowledge(n.requiredKnowledge);
  let claim: DiagnosticNode["claim"] = null;
  if (n.claim !== null) {
    const c = record(n.claim,["context","type"]);
    if (!Array.isArray(c.context)) throw Error("invalid context");
    const context: Labels[] = [];
    for (const t of c.context) context.push(decodeLabels(t,size));
    claim = { context, type: decodeLabels(c.type,size) };
  }
  return { label, sourceMap: map, requiredKnowledge, claim, node: n.node === null ? null : decodeNode(n.node) };
}

export function readDiagnostic(
  detail: string,
): ObligationDiagnostic | undefined {
  const lines = detail.split(/\r?\n/).filter((line) => line.startsWith(PREFIX));
  if (lines.length !== 1) return undefined;
  try {
    const parsed: Json = JSON.parse(lines[0].slice(PREFIX.length));
    if (!isParsedObject(parsed) || illFormedString(parsed)) return undefined;
    const d = parsed;
    const kind = d.kind;
    if (typeof kind !== "string") return undefined;
    // Looked up at the parsed kind in a Map, which holds no inherited member.
    const fields = new Map<string, readonly string[]>(KIND_FIELDS).get(kind);
    if (!fields) return undefined;
    record(d,["phase","outcome","fuel","types","kind",...fields],["requiredResult","names","candidatesLeftOut"]);
    const outcome = diagnosticOutcome(d.outcome);
    // The graph decides how many labels there are, so it is decoded first and
    // everything after counts against what it returned.
    const wireTypes = d.types;
    const types = decodeGraph(wireTypes);
    const names: [number, string][] = [];
    if (d.names !== undefined) {
      if (!Array.isArray(d.names) || !d.names.length) return undefined;
      let previous = -1;
      for (const entry of d.names) {
        if (!Array.isArray(entry) || entry.length !== 2) return undefined;
        const [row, name] = entry;
        if (typeof name !== "string" || !name) return undefined;
        if (typeof row !== "number") return undefined;
        nat(row);
        if (row <= previous || row >= types.length) return undefined;
        previous = row;
        names.push([row, name]);
      }
    }
    // The decoded parts replace their wire forms in the result.
    const source = d.source === undefined ? undefined : diagnosticNode(d.source,types.length);
    const destinationNode = d.destination === undefined ? undefined : diagnosticNode(d.destination,types.length);
    const map = d.sourceMap === undefined ? undefined : sourceMap(d.sourceMap);
    let judgment: DirectJudgment | undefined;
    if (kind === "direct-obligation") {
      judgment = directJudgment(d.judgment,types.length);
      const at = judgment.subject;
      const map = d.sourceMap;
      if (!isParsedObject(map)) return undefined;
      const pos = map.pos, context = map.context;
      if (!Array.isArray(pos) || !Array.isArray(context) ||
          pos[0] !== at[0] || pos[1] !== at[1] || context.length !== 0)
        return undefined;
    }
    if (kind === "source-refusal" && typeof d.reason !== "string") return undefined;
    if (kind === "production-failure" && typeof d.failure !== "string") return undefined;
    const labels = (v: Json) => decodeLabels(v,types.length);
    const requiredResult = d.requiredResult === undefined ? undefined : labels(d.requiredResult);
    const candidatesLeftOut = d.candidatesLeftOut === undefined ? undefined : leftOut(d.candidatesLeftOut);
    let sequent: Sequent | undefined;
    if (kind === "node-typing" || kind === "expression-claim") {
      const q = d.sequent;
      if (!isParsedObject(q) || Object.keys(q).sort().join() !== "context,term,type" || !Array.isArray(q.context)) return undefined;
      const context: Labels[] = [];
      for (const t of q.context) context.push(labels(t));
      const type = q.type;
      if (type === undefined) return undefined;
      const decodedType = labels(type);
      sequent = { context, type: decodedType, term: decodeTerm(q.term) };
    }
    let decodedTransfer: DiagnosticTransfer | undefined;
    if (kind === "edge-coverage") {
      nat(d.edgeIndex);
      const transfer = record(d.transfer,["available","target","booleanObservation","tagObservation"]);
      const target = record(transfer.target,["label","mapping"]);
      let tagObservation: DiagnosticTransfer["tagObservation"] = null;
      if (transfer.tagObservation !== null) {
        const tag = record(transfer.tagObservation,["test","answer","slot"]);
        const slot = nat(tag.slot);
        if (typeof tag.answer !== "boolean") return undefined;
        tagObservation = { slot, answer: tag.answer, test: decodeTag(tag.test) };
      }
      const destination = record(d.destination,["label","sourceMap","node","claim","requiredKnowledge"]);
      const claim = destination.claim;
      const available = transfer.available;
      if (!isParsedObject(claim)) return undefined;
      const context = claim.context;
      if (!Array.isArray(available) || !Array.isArray(context)) return undefined;
      const decodedAvailable: Labels[] = [];
      for (const t of available) decodedAvailable.push(labels(t));
      context.forEach(labels);
      const targetLabel = target.label;
      if (typeof targetLabel !== "number" || !Number.isSafeInteger(targetLabel)) return undefined;
      const mapping = target.mapping;
      let decodedMapping: number[] | null = null;
      if (mapping !== null) {
        if (!Array.isArray(mapping)) return undefined;
        const indices: number[] = [];
        for (const i of mapping) {
          if (typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= available.length) return undefined;
          indices.push(i);
        }
        decodedMapping = indices;
      }
      if (transfer.booleanObservation !== null && typeof transfer.booleanObservation !== "boolean") return undefined;
      decodedTransfer = { available: decodedAvailable,
        target: { label: targetLabel, mapping: decodedMapping },
        booleanObservation: transfer.booleanObservation, tagObservation };
    }
    const fuel = d.fuel;
    if (
      !PHASES.includes(d.phase) ||
      !Array.isArray(wireTypes) ||
      typeof fuel !== "number" ||
      !Number.isSafeInteger(fuel) ||
      fuel < 0
    )
      return undefined;
    if (kind !== "production-failure" && typeof d.id !== "string")
      return undefined;
    if (kind === "edge-coverage" && (!d.source || !d.destination || !d.transfer))
      return undefined;
    if ((kind === "node-typing" || kind === "expression-claim") && !d.sequent)
      return undefined;
    const phase: Phase = d.phase === "proof-search" ? "proof-search" :
      d.phase === "certificate-check" ? "certificate-check" : "request-validation";
    const common: Common = { phase, outcome, fuel, types: wireTypes,
      ...(d.names === undefined ? {} : { names }),
      ...(requiredResult === undefined ? {} : { requiredResult }),
      ...(candidatesLeftOut === undefined ? {} : { candidatesLeftOut }) };
    if (kind === "production-failure" && typeof d.failure === "string") {
      const result: ProductionFailure = { ...common, kind: "production-failure", failure: d.failure };
      return result;
    }
    const id = d.id;
    if (typeof id !== "string") return undefined;
    if (kind === "node-typing" && source && sequent) {
      const result: NodeTyping = { ...common, kind: "node-typing", id, source, sequent };
      return result;
    }
    if (kind === "expression-claim" && map && sequent) {
      const result: ExpressionClaimFailure = { ...common, kind: "expression-claim", id, sourceMap: map, sequent };
      return result;
    }
    if (kind === "direct-obligation" && map && judgment) {
      const result: DirectObligationFailure = { ...common, kind: "direct-obligation", id, sourceMap: map, judgment };
      return result;
    }
    if (kind === "source-refusal" && map && typeof d.reason === "string") {
      const result: SourceRefusal = { ...common, kind: "source-refusal", id, sourceMap: map, reason: d.reason };
      return result;
    }
    if (kind === "edge-coverage" && source && destinationNode && decodedTransfer) {
      const result: EdgeCoverage = { ...common, kind: "edge-coverage", id, edgeIndex: nat(d.edgeIndex), source,
        destination: destinationNode, transfer: decodedTransfer };
      return result;
    }
    return undefined;
  } catch (error) {
    passToolFailure(error);
    return undefined;
  }
}
