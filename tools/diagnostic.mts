import { decodeGraph, decodeLabels, type TypeGraph, type Labels, type Clause } from "./type-graph.mts";
// calculus.mts decodes the native terms a record's judgements and source map name.
// control-flow.mts decodes the program-graph node a node or edge obligation names.
import { decodeTag, decodeTerm, type Json, type Tag, type Term } from "./calculus.mts";
import { decodeNode, type ProgramNode } from "./control-flow.mts";
import type { Span } from "./span.mts";

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

/** An assertion about a runtime slot: for a cell, about the named field of the
 * object it holds; for a value, about the slot itself, where the field is not
 * consulted. */
type HeapAtom = "nul" | "undef" | "tru" | "fls" | "num" | "str" | "defined" | "nonNull" | "nonNullish" |
  Extract<Clause, {numLit: unknown} | {strLit: unknown}> |
  /** A test's observed answer. */
  {tag: {test: Tag; answer: boolean}};
const HEAP_ATOMS: Record<Extract<HeapAtom, string>, true> = {
  nul: true, undef: true, tru: true, fls: true, num: true, str: true, defined: true, nonNull: true, nonNullish: true,
};
const heapAtoms: readonly Json[] = Object.keys(HEAP_ATOMS);
function heapAtom(v: Json): void {
  if (heapAtoms.includes(v)) return;
  // Singleton payloads use the graph language's existing decoder.
  if (isRecord(v) && "strLit" in v) {
    decodeGraph([[{strLit: record(v,["strLit"]).strLit}]]);
    return;
  }
  if (isRecord(v) && "tag" in v) {
    const t = record(record(v,["tag"]).tag,["test","answer"]);
    decodeTag(t.test);
    if (typeof t.answer !== "boolean") throw Error("invalid tag atom answer");
    return;
  }
  const a = record(v,["numLit"]);
  decodeGraph([[{numLit: a.numLit}]]);
}
interface HeapFact {
  slot: number;
  contents: HeapAtom[];
  field: string;
}
export interface HeapKnowledge {
  cells: HeapFact[]; values: HeapFact[];
  /** A read link (`alias` false), a value equality (`alias` true), or, with
   * `distinct`, two fields at different locations: `cell.field` and
   * `value.other`. A read link through an `optional` key also covers the
   * object lacking the key, where the read gave `undefined`. */
  links: {cell: number; value: number; alias: boolean; field: string; distinct: boolean; other: string; optional: boolean}[];
}

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

function diagnosticOutcome(value: Json | undefined): void {
  if (!isRecord(value)) throw Error("invalid diagnostic outcome");
  switch (value.kind) {
    case "not-established": record(value, ["kind"]); return;
    case "exhausted": {
      const outcome = record(value, ["kind", "resource"]);
      const resource = record(outcome.resource, ["kind", "limit", "rounds", "visited"]);
      if (resource.kind !== "subtype-frontier") throw Error("unknown search resource");
      nat(resource.limit); nat(resource.rounds); nat(resource.visited);
      if (Number(resource.rounds) > Number(resource.limit)) throw Error("resource counts exceed budget");
      return;
    }
    default: throw Error("unknown diagnostic outcome");
  }
}

/** What every record carries, whatever the failure was. */
interface Common {
  phase: Phase;
  outcome: DiagnosticOutcome;
  /** The proof budget the search was given. */
  fuel: number;
  /** The store's labels the record mentions, projected onto a finite table. */
  types: TypeGraph;
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
const KINDS: readonly (Json | undefined)[] = [
  "node-typing",
  "edge-coverage",
  "expression-claim",
  "direct-obligation",
  "source-refusal",
  "production-failure",
];
const PREFIX = "obligation-diagnostic: ";

/** A parsed object: the record is read from `JSON.parse`'s data. */
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
function record(v: Json | undefined, required: string[], optional: string[] = []): Fields {
  if (!isRecord(v) || required.some(k => !(k in v)) || Object.keys(v).some(k => ![...required,...optional].includes(k))) throw Error("invalid diagnostic fields");
  return v;
}
function nat(v: Json | undefined): void { if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0) throw Error("invalid diagnostic index"); }
function span(v: Json | undefined): asserts v is Span {
  if (!Array.isArray(v) || v.length !== 2) throw Error("invalid diagnostic span");
  const [start, end] = v;
  nat(start); nat(end);
  if (typeof start !== "number" || typeof end !== "number" || end < start) throw Error("reversed span");
}
function sourceMap(v: Json | undefined): void {
  if (v === null) return;
  const m = record(v,["pos","role","environmentStart","context"]);
  span(m.pos); if (typeof m.role !== "string") throw Error("invalid role");
  if (m.environmentStart !== null) nat(m.environmentStart);
  if (!Array.isArray(m.context)) throw Error("invalid source context");
  for (const entry of m.context) {
    const d = record(entry,["name","span"]);
    if (typeof d.name !== "string") throw Error("invalid binding name");
    if (d.span !== null) span(d.span);
  }
}

function directJudgment(v: Json | undefined, size: number): DirectJudgment {
  const j = record(v,["kind","subject","actual","expected"]);
  if (j.kind !== "subtyping") throw Error("unknown direct-obligation judgment");
  const subject = j.subject;
  span(subject);
  return {kind:"subtyping",subject,
    actual:decodeLabels(j.actual,size),expected:decodeLabels(j.expected,size)};
}
function knowledge(v: Json | undefined): void {
  if (v === null) return;
  const k = record(v,["cells","values","links"]);
  for (const key of ["cells","values"]) {
    const facts = k[key];
    if (!Array.isArray(facts)) throw Error("invalid heap facts");
    for (const fact of facts) {
      const f = record(fact,["slot","contents","field"]); nat(f.slot);
      if (typeof f.field !== "string") throw Error("invalid heap fact field");
      if (!Array.isArray(f.contents)) throw Error("invalid heap contents");
      f.contents.forEach(heapAtom);
    }
  }
  if (!Array.isArray(k.links)) throw Error("invalid heap links");
  for (const link of k.links) {
    const l = record(link,["cell","value","alias","field","distinct","other","optional"]); nat(l.cell); nat(l.value);
    if (typeof l.distinct !== "boolean") throw Error("invalid distinct flag");
    if (typeof l.optional !== "boolean") throw Error("invalid optional flag");
    if (typeof l.other !== "string") throw Error("invalid link field");
    if (typeof l.field !== "string") throw Error("invalid heap link field");
    if (typeof l.alias !== "boolean") throw Error("invalid alias");
  }
}
/** A node record with its node decoded in place of its wire form, as the
 * term and tag below are. */
function diagnosticNode(v: Json | undefined, size: number): { node: ProgramNode | null } {
  const n = record(v,["label","sourceMap","node","claim","requiredKnowledge"]);
  nat(n.label); sourceMap(n.sourceMap); knowledge(n.requiredKnowledge);
  if (n.claim !== null) {
    const c = record(n.claim,["context","type"]);
    if (!Array.isArray(c.context)) throw Error("invalid context");
    c.context.forEach(t => decodeLabels(t,size)); decodeLabels(c.type,size);
  }
  return { ...n, node: n.node === null ? null : decodeNode(n.node) };
}

export function readDiagnostic(
  detail: string,
): ObligationDiagnostic | undefined {
  const lines = detail.split(/\r?\n/).filter((line) => line.startsWith(PREFIX));
  if (lines.length !== 1) return undefined;
  // The decoded parts replace their wire forms in the result.
  let result: { [key: string]: unknown };
  try {
    const parsed: Json = JSON.parse(lines[0].slice(PREFIX.length));
    if (!isRecord(parsed)) return undefined;
    const d = parsed;
    const variants: Record<string,string[]> = {
      "node-typing":["id","source","sequent"], "expression-claim":["id","sourceMap","sequent"],
      "direct-obligation":["id","sourceMap","judgment"],
      "source-refusal":["id","sourceMap","reason"],
      "edge-coverage":["id","edgeIndex","source","destination","transfer"], "production-failure":["failure"],
    };
    const kind = d.kind;
    if (typeof kind !== "string") return undefined;
    const fields = variants[kind];
    if (!fields) return undefined;
    record(d,["phase","outcome","fuel","types","kind",...fields],["requiredResult","names"]);
    diagnosticOutcome(d.outcome);
    // The graph decides how many labels there are, so it is decoded first and
    // everything after counts against what it returned.
    const types = decodeGraph(d.types);
    if (d.names !== undefined) {
      if (!Array.isArray(d.names) || !d.names.length) return undefined;
      let previous = -1;
      for (const entry of d.names) {
        if (!Array.isArray(entry) || entry.length !== 2 || typeof entry[1] !== "string" || !entry[1]) return undefined;
        const [row] = entry;
        if (typeof row !== "number") return undefined;
        nat(row);
        if (row <= previous || row >= types.length) return undefined;
        previous = row;
      }
    }
    result = { ...d };
    if (d.source !== undefined) result.source = diagnosticNode(d.source,types.length);
    if (d.destination !== undefined) result.destination = diagnosticNode(d.destination,types.length);
    if (d.sourceMap !== undefined) sourceMap(d.sourceMap);
    if (kind === "direct-obligation") {
      const judgment = directJudgment(d.judgment,types.length);
      const at = judgment.subject;
      const map = d.sourceMap;
      if (!isRecord(map)) return undefined;
      const pos = map.pos, context = map.context;
      if (!Array.isArray(pos) || !Array.isArray(context) ||
          pos[0] !== at[0] || pos[1] !== at[1] || context.length !== 0)
        return undefined;
      result.judgment = judgment;
    }
    if (kind === "source-refusal" && typeof d.reason !== "string") return undefined;
    if (kind === "production-failure" && typeof d.failure !== "string") return undefined;
    const labels = (v: Json) => decodeLabels(v,types.length);
    if (d.requiredResult !== undefined) labels(d.requiredResult);
    if (kind === "node-typing" || kind === "expression-claim") {
      const q = d.sequent;
      if (!isRecord(q) || Object.keys(q).sort().join() !== "context,term,type" || !Array.isArray(q.context)) return undefined;
      q.context.forEach(labels);
      const type = q.type;
      if (type === undefined) return undefined;
      labels(type);
      result.sequent = { ...q, term: decodeTerm(q.term) };
    }
    if (kind === "edge-coverage") {
      nat(d.edgeIndex);
      const transfer = record(d.transfer,["available","target","booleanObservation","tagObservation"]);
      const target = record(transfer.target,["label","mapping"]);
      if (transfer.tagObservation !== null) {
        const tag = record(transfer.tagObservation,["test","answer","slot"]);
        nat(tag.slot);
        if (typeof tag.answer !== "boolean") return undefined;
        result.transfer = { ...transfer, tagObservation: { ...tag, test: decodeTag(tag.test) } };
      }
      const destination = record(d.destination,["label","sourceMap","node","claim","requiredKnowledge"]);
      const claim = destination.claim;
      const available = transfer.available;
      if (!isRecord(claim) || !Array.isArray(available) || !Array.isArray(claim.context)) return undefined;
      available.forEach(labels); claim.context.forEach(labels);
      if (typeof target.label !== "number" || !Number.isSafeInteger(target.label)) return undefined;
      const mapping = target.mapping;
      if (mapping !== null && (!Array.isArray(mapping) || mapping.some(i => typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= available.length))) return undefined;
      if (transfer.booleanObservation !== null && typeof transfer.booleanObservation !== "boolean") return undefined;
    }
    if (
      !PHASES.includes(d.phase) ||
      !Array.isArray(d.types) ||
      typeof d.fuel !== "number" ||
      !Number.isSafeInteger(d.fuel) ||
      d.fuel < 0
    )
      return undefined;
    if (!KINDS.includes(kind)) return undefined;
    if (kind !== "production-failure" && typeof d.id !== "string")
      return undefined;
    if (kind === "edge-coverage" && (!d.source || !d.destination || !d.transfer))
      return undefined;
    if ((kind === "node-typing" || kind === "expression-claim") && !d.sequent)
      return undefined;
  } catch {
    return undefined;
  }
  // asserted: the decoder's result, checked field by field and variant by variant above
  return result as unknown as ObligationDiagnostic;
}
