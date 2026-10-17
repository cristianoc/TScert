import { decodeGraph, decodeLabels, type TypeGraph, type Labels, type Clause } from "./type-graph.mts";
// calculus.mts decodes the native terms a record's judgements and source map name.
// control-flow.mts decodes the program-graph node a node or edge obligation names.
import { decodeTag, decodeTerm, type Tag, type Term } from "./calculus.mts";
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
  Extract<Clause, {numLit: unknown} | {strLit: unknown}>;
const HEAP_ATOMS: Record<Extract<HeapAtom, string>, true> = {
  nul: true, undef: true, tru: true, fls: true, num: true, str: true, defined: true, nonNull: true, nonNullish: true,
};
const heapAtoms: readonly unknown[] = Object.keys(HEAP_ATOMS);
function heapAtom(v: unknown): void {
  if (heapAtoms.includes(v)) return;
  // Singleton payloads use the graph language's existing decoder.
  if (typeof v === "object" && v !== null && "strLit" in v) {
    decodeGraph([[{strLit: record(v,["strLit"]).strLit}]]);
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

function diagnosticOutcome(value: unknown): void {
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

const PHASES: readonly unknown[] = [
  "proof-search",
  "certificate-check",
  "request-validation",
];
const KINDS: readonly unknown[] = [
  "node-typing",
  "edge-coverage",
  "expression-claim",
  "direct-obligation",
  "source-refusal",
  "production-failure",
];
const PREFIX = "obligation-diagnostic: ";

const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object" && !Array.isArray(v);
function record(v: unknown, required: string[], optional: string[] = []): Record<string, unknown> {
  if (!isRecord(v) || required.some(k => !(k in v)) || Object.keys(v).some(k => ![...required,...optional].includes(k))) throw Error("invalid diagnostic fields");
  return v;
}
function nat(v: unknown) { if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0) throw Error("invalid diagnostic index"); }
function span(v: unknown): asserts v is Span { if (!Array.isArray(v) || v.length !== 2) throw Error("invalid diagnostic span"); v.forEach(nat); if (v[1] < v[0]) throw Error("reversed span"); }
function sourceMap(v: unknown): asserts v is SourceMapEntry | null {
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

function directJudgment(v: unknown, size: number): DirectJudgment {
  const j = record(v,["kind","subject","actual","expected"]);
  if (j.kind !== "subtyping") throw Error("unknown direct-obligation judgment");
  span(j.subject);
  return {kind:"subtyping",subject:j.subject,
    actual:decodeLabels(j.actual,size),expected:decodeLabels(j.expected,size)};
}
function knowledge(v: unknown) {
  if (v === null) return;
  const k = record(v,["cells","values","links"]);
  for (const key of ["cells","values"]) {
    if (!Array.isArray(k[key])) throw Error("invalid heap facts");
    for (const fact of k[key]) {
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
function diagnosticNode(v: unknown, size: number) {
  const n = record(v,["label","sourceMap","node","claim","requiredKnowledge"]);
  nat(n.label); sourceMap(n.sourceMap); knowledge(n.requiredKnowledge);
  if (n.claim !== null) {
    const c = record(n.claim,["context","type"]);
    if (!Array.isArray(c.context)) throw Error("invalid context");
    c.context.forEach(t => decodeLabels(t,size)); decodeLabels(c.type,size);
  }
  // The decoded node replaces its wire form, as the term and tag below do.
  if (n.node !== null) n.node = decodeNode(n.node);
}

export function readDiagnostic(
  detail: string,
): ObligationDiagnostic | undefined {
  const lines = detail.split(/\r?\n/).filter((line) => line.startsWith(PREFIX));
  if (lines.length !== 1) return undefined;
  let d: Record<string, unknown>;
  try {
    const parsed: unknown = JSON.parse(lines[0].slice(PREFIX.length));
    if (!isRecord(parsed)) return undefined;
    d = parsed;
    const variants: Record<string,string[]> = {
      "node-typing":["id","source","sequent"], "expression-claim":["id","sourceMap","sequent"],
      "direct-obligation":["id","sourceMap","judgment"],
      "source-refusal":["id","sourceMap","reason"],
      "edge-coverage":["id","edgeIndex","source","destination","transfer"], "production-failure":["failure"],
    };
    if (typeof d.kind !== "string" || !variants[d.kind]) return undefined;
    record(d,["phase","outcome","fuel","types","kind",...variants[d.kind]],["requiredResult","names"]);
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
        nat(row);
        if (row <= previous || row >= types.length) return undefined;
        previous = row;
      }
    }
    if (d.source !== undefined) diagnosticNode(d.source,types.length);
    if (d.destination !== undefined) diagnosticNode(d.destination,types.length);
    if (d.sourceMap !== undefined) sourceMap(d.sourceMap);
    if (d.kind === "direct-obligation") {
      const judgment = directJudgment(d.judgment,types.length);
      const at = judgment.subject;
      const map = d.sourceMap;
      if (map === null || map === undefined) return undefined;
      if (map.pos[0] !== at[0] || map.pos[1] !== at[1] || map.context.length !== 0)
        return undefined;
      d.judgment = judgment;
    }
    if (d.kind === "source-refusal" && typeof d.reason !== "string") return undefined;
    if (d.kind === "production-failure" && typeof d.failure !== "string") return undefined;
    const labels = (v: unknown) => decodeLabels(v,types.length);
    if (d.requiredResult !== undefined) labels(d.requiredResult);
    if (d.kind === "node-typing" || d.kind === "expression-claim") {
      const q = d.sequent;
      if (!isRecord(q) || Object.keys(q).sort().join() !== "context,term,type" || !Array.isArray(q.context)) return undefined;
      q.context.forEach(labels); labels(q.type); q.term = decodeTerm(q.term);
    }
    if (d.kind === "edge-coverage") {
      nat(d.edgeIndex);
      const transfer = record(d.transfer,["available","target","booleanObservation","tagObservation"]);
      const target = record(transfer.target,["label","mapping"]);
      if (transfer.tagObservation !== null) {
        const tag = record(transfer.tagObservation,["test","answer","slot"]);
        nat(tag.slot);
        tag.test = decodeTag(tag.test);
        if (typeof tag.answer !== "boolean") return undefined;
      }
      const destination = record(d.destination,["label","sourceMap","node","claim","requiredKnowledge"]);
      const claim = destination.claim;
      const available = transfer.available;
      if (!isRecord(claim) || !Array.isArray(available) || !Array.isArray(claim.context)) return undefined;
      available.forEach(labels); claim.context.forEach(labels);
      if (!Number.isSafeInteger(target.label)) return undefined;
      const mapping = target.mapping;
      if (mapping !== null && (!Array.isArray(mapping) || mapping.some(i => typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= available.length))) return undefined;
      if (transfer.booleanObservation !== null && typeof transfer.booleanObservation !== "boolean") return undefined;
    }
  } catch {
    return undefined;
  }
  if (
    !PHASES.includes(d.phase) ||
    !Array.isArray(d.types) ||
    typeof d.fuel !== "number" ||
    !Number.isSafeInteger(d.fuel) ||
    d.fuel < 0
  )
    return undefined;
  if (!KINDS.includes(d.kind)) return undefined;
  if (d.kind !== "production-failure" && typeof d.id !== "string")
    return undefined;
  if (d.kind === "edge-coverage" && (!d.source || !d.destination || !d.transfer))
    return undefined;
  if (
    (d.kind === "node-typing" || d.kind === "expression-claim") &&
    !d.sequent
  )
    return undefined;
  // asserted: the decoder's result, checked field by field and variant by variant above
  return d as unknown as ObligationDiagnostic;
}
