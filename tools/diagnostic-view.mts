/* Reading the verifier's diagnostic record for display.
 *
 * A record describes an unsuccessful verification attempt: the assumptions that
 * were available and the conclusion that had to follow. It is explanatory
 * metadata, never proof evidence and never a judgement that a claim is false.
 * See docs/OBLIGATION-DIAGNOSTICS.md.
 */

import { isJsonList, isJsonObject, type CallCode, type JsonRead, type JsonValue, type Term } from "./calculus.mts";
import surface from "./claim-text.mts";
import type { DiagnosticOutcome, HeapKnowledge, EdgeFacts, ObligationDiagnostic, ReturnFacts, SourceMapEntry, StepPreconditions } from "./diagnostic.mts";
import { indexFact, knowledgeFacts } from "./fact-text.mts";

/** How a context binding is named in the source, as a source map states it. */
type Descriptor = SourceMapEntry["context"][number];

/* A record reaches `presentObligation` decoded: diagnostic.mts checks one field
 * by field and refuses what does not fit, so the shapes below are the ones that
 * arrive. A label list read from it is a `JsonValue`, and reading one narrows
 * what arrived instead of assuming it. */

/**
 * What the verifier had and what had to follow from it, in source names.
 * Explanatory metadata about an unsuccessful attempt — never evidence, and
 * never a statement that a claim is false.
 */
interface ObligationSummary {
  /** Source-named explanation of the obligation, where the record supports one. */
  summary?: string;
  /** How the search ended. */
  searchOutcome: string;
}

/** Resource exhaustion is distinct from an unsuccessful completed search. */
function searchOutcome(outcome: DiagnosticOutcome, fuel: number): string {
  switch (outcome.kind) {
    case "exhausted":
      return `Subtype search exhausted after ${outcome.resource.rounds} frontier rounds (limit ${outcome.resource.limit}); ${outcome.resource.visited} comparisons visited. The judgment is inconclusive.`;
    case "not-established":
      return `Search depth: ${fuel}. No derivation was found; this does not prove the claim false.`;
  }
}

/* ---------- types ---------- */
// A type is a list of labels into the record's own table, read as their union
// and printed in the one surface syntax every claim is shown in: lifted into
// the structural encoding and printed from there. A row the table names (a
// diagnostic's `names`) is shown by its name.
/** A type a record mentions, through the record's table and names. */
interface Table {
  readonly types: JsonValue;
  readonly names?: readonly (readonly [number, string])[];
}
function recordType(table: Table, labels: JsonRead): string {
  if (!isJsonList(labels)) return "(no type recorded)";
  return surface.printType(surface.lift(table.types, labels, 3, table.names ?? [])).text;
}

/* ---------- source maps ---------- */
// A descriptor says how one context binding is named in the source: a binding
// name, or the expression whose value it holds. Lowering guarantees one of the
// two for every binding and fails rather than emit a context it cannot describe,
// so a position should never reach a reader. The `slot N` fallback below is for
// a record that arrives without a source map at all; seeing one means
// lowering broke that invariant.
// A name lowering makes up for a value no source binding holds (`%next@264%`,
// `.path:0`) is shown by the source expression it holds where the descriptor
// gives one.
function bindingText(descriptor: Descriptor, source: string): string {
  const span = descriptor.span;
  const spanned = span === null ? "" : source.slice(span[0], span[1]).replace(/\s+/g, " ").trim();
  if (descriptor.name && (/^[A-Za-z_$][\w$]*(\.[A-Za-z_$][\w$]*)*$/.test(descriptor.name) || spanned === ""))
    return descriptor.name;
  return spanned;
}

/** A point's source span as the text it covers, quoted, or `other` where it
 * has no source map. */
const spanText = (map: SourceMapEntry | null, source: string, other: string): string =>
  map === null ? other : `«${source.slice(map.pos[0], map.pos[1]).replace(/\s+/g, " ").trim()}»`;

const bindingsOf = (map: SourceMapEntry | null, source: string): string[] =>
  (map === null ? [] : map.context).map((d) => bindingText(d, source));

/** Whether a node or edge end required any fact of the heap as it is. */
const requiresKnowledge = (knowledge: HeapKnowledge | null): boolean =>
  !!knowledge && knowledge.cells.length + knowledge.values.length + knowledge.links.length + knowledge.elems.length + knowledge.indices.length > 0;

const sameType = (a: JsonRead, b: JsonRead): boolean =>
  a === undefined || b === undefined ? a === b : JSON.stringify(a) === JSON.stringify(b);

/* ---------- terms ---------- */
/** A part of a term: a term, a list of terms, or call code. */
type TermPart = { k: "term"; t: Term } | { k: "terms"; ts: Term[] } | { k: "code"; c: CallCode };

/** A term's parts, in the order of their field names: the one traversal of
 * the term grammar the summary reads. */
function termParts(t: Term): TermPart[] {
  const one = (x: Term): TermPart => ({ k: "term", t: x });
  const list = (xs: Term[]): TermPart => ({ k: "terms", ts: xs });
  const code = (c: CallCode): TermPart => ({ k: "code", c });
  switch (t.kind) {
    case "nul": case "undef": case "tru": case "fls": case "num": case "str": case "bigint": case "sym": case "var": case "arr": return [];
    case "invoke": return [list(t.args), one(t.f), one(t.r)];
    case "construct": return [list(t.args), one(t.f)];
    case "letE": case "writeAt": case "arith": case "merge": return [one(t.a), one(t.b)];
    case "objAt": return [code(t.call)];
    case "makeAt": return [code(t.call), list(t.inits)];
    case "readAt": case "test": case "lenOf": case "spread": case "throw": return [one(t.a)];
    case "indexAt": return [one(t.a), one(t.key)];
    case "ite": return [one(t.c), one(t.e), one(t.t)];
    case "arrLit": return [list(t.inits)];
    case "elemAt": return [one(t.a), one(t.i)];
    case "setElem": return [one(t.a), one(t.i), one(t.v)];
    case "makeKey": return [one(t.init), one(t.key)];
    case "goto": return [one(t.dflt), list(t.env), list(t.exprs)];
    case "frame": return [one(t.dflt), list(t.env), list(t.exprs), one(t.t)];
    default: { const exhaustive: never = t; return exhaustive; }
  }
}

/** Call code's terms, in the order of their field names; a list of terms
 * it holds is not among them. */
function codeTerms(c: CallCode): Term[] {
  switch (c.kind) {
    case "absent": case "graph": return [];
    case "bound": return [c.receiver, c.target];
    default: { const exhaustive: never = c; return exhaustive; }
  }
}

/* ---------- facts ---------- */
/** A point's slots in source names: a slot of its context by its binding,
 * one past the context by the read or alias link that gives its value, else
 * by its position. */
function slotNamer(links: HeapKnowledge["links"], binding: (slot: number) => string, width: number): (slot: number) => string {
  const name = (slot: number, seen: ReadonlySet<number>): string => {
    if (slot < width) return binding(slot);
    const link = links.find((l) => l.value === slot && l.cell !== slot && !seen.has(l.cell));
    if (link === undefined) return "slot " + slot;
    const cell = name(link.cell, new Set([...seen, slot]));
    const field = typeof link.field === "string" ? link.field : `[Symbol ${link.field.symbol}]`;
    return link.alias ? cell : `${cell}${link.optional ? "?." : "."}${field}`;
  };
  return (slot: number): string => name(slot, new Set());
}

/** Whether a type, lifted, is a variable's cell: one record, of no index
 * and no prototype, whose one field is `value`, the field a cell holds its
 * variable's value in (`valueField`). */
function isCell(table: Table, labels: JsonRead): boolean {
  if (!isJsonList(labels)) return false;
  const lifted = surface.lift(table.types, labels, 1, table.names ?? []);
  if (!isJsonObject(lifted)) return false;
  const atoms = lifted["atoms"];
  if (!isJsonList(atoms) || atoms.length !== 1) return false;
  const record = atoms[0];
  if (!isJsonObject(record) || record["a"] !== "record") return false;
  const fields = record["fields"];
  return isJsonList(fields) && fields.length === 1 && isJsonObject(fields[0]) && fields[0]["name"] === "value";
}

/** The facts of a knowledge but its links (which name its slots), each
 * once, in source names, but the texts of `except`; a variable's cell (of
 * the slots `variable` states) by the variable's binding. */
function factsText(k: HeapKnowledge, named: (slot: number) => string, except: readonly string[] = [],
    variable: (slot: number) => boolean = () => false): string[] {
  return [...new Set(knowledgeFacts(k, named, variable).filter((f) => f.kind !== "link").map((f) => f.text))]
    .filter((t) => !except.includes(t));
}

/** Facts as one conjunction: a disjunction, guarded or conditional fact in
 * parentheses where there is more than one. */
const conjunction = (facts: readonly string[]): string =>
  facts.length < 2 ? facts.join("") : facts.map((f) => (/ \|\| | → /.test(f) ? `(${f})` : f)).join(" && ");

/** A refused step's preconditions in source names: each precondition's
 * requirements that do not hold, then the facts known over the step's
 * slots. */
function preconditionsText(pre: StepPreconditions, binding: (slot: number) => string, width: number): string {
  const named = slotNamer(pre.known.links, binding, width);
  const missing = pre.signatures.map((sig) => [
    ...(sig.requires !== null && !sig.requires.entailed
      ? [`every element of ${named(sig.requires.slot)} is ${sig.requires.pred.join(" | ")}`] : []),
    ...sig.atoms.filter((a) => !a.entailed).map((a) =>
      a.fact === null ? "a fact over a position the call holds no slot for" : indexFact(a.fact, named) ?? "true"),
  ]).filter((m) => m.length > 0);
  const subject = pre.step === "write" ? "This write" :
    pre.signatures.length > 1 ? "A signature of the callee" : "The callee";
  const requirement = missing.map((m) =>
    `${subject} requires ${conjunction(m)}, which the facts here do not establish.`);
  // (its index and elements facts: what a precondition reads)
  const known = factsText({ ...pre.known, cells: [], values: [], separation: { depth: 0, facts: [] } }, named);
  return [...requirement,
    known.length ? `Known over its operands: ${known.join(", ")}.` : "No fact is known over its operands."].join(" ");
}

/** A refused edge's facts in source names, at its target's slots: the edge
 * by its source's span, what the target requires that it does not
 * establish, the required facts it does establish, then the other facts it
 * holds over the same slots; none where it names no requirement it does not
 * establish. */
function edgeFactsText(facts: EdgeFacts, from: string, binding: (slot: number) => string, width: number,
    variable: (slot: number) => boolean): string | undefined {
  const named = slotNamer([...facts.known.links, ...facts.lacking.links, ...facts.established.links], binding, width);
  const r = facts.requirement;
  const lacking = r.kind === "facts" ? factsText(facts.lacking, named, [], variable)
    : r.kind === "implication" ? [`the implication from ${named(r.test)} to the type it states of ${named(r.target)}`]
    : r.kind === "input-value" ? [`that ${named(r.slot)} holds the entry value of the function's input ${r.input + 1}`]
    : [`that ${named(r.slot)} holds the input the promise is about`];
  if (lacking.length === 0) return undefined;
  const established = factsText(facts.established, named, [], variable);
  const known = factsText(facts.known, named, established, variable);
  return [`The edge from ${from} does not establish ${conjunction(lacking)}, which the next point requires.`,
    ...(established.length ? [`It establishes ${established.join(", ")}.`] : []),
    known.length ? `Known on the edge over the same slots${established.length ? ", beside those" : ""}: ${known.join(", ")}.`
      : `No other fact is known on the edge over the same slots.`].join(" ");
}

/** A return refused for its postcondition, in source names over its pushed
 * slots (the result at 0): the postcondition's facts it does not establish,
 * then the return's facts. */
function postconditionText(post: ReturnFacts, binding: (slot: number) => string, width: number): string | undefined {
  const named = slotNamer(post.known.links, (slot) => (slot === 0 ? "result" : binding(slot - 1)), width + 1);
  const lacking = post.facts.filter((f) => !f.entailed).map((f) =>
    f.fact === null ? "a fact over an input whose entry value no slot holds" : indexFact(f.fact, named) ?? "true");
  if (lacking.length === 0) return undefined;
  const known = factsText(post.known, named);
  return `This return does not establish ${conjunction(lacking)} of the postcondition. ` +
    (known.length ? `Known at the return: ${known.join(", ")}.` : "No fact is known at the return over those slots.");
}

/** Uniform report contract: the source-named summary of a failed obligation and
 * how its search ended, as strings a report shows without decoding the
 * calculus or applying slot transfers. */
export function presentObligation(ob: ObligationDiagnostic, source: string): ObligationSummary {
  const searched = searchOutcome(ob.outcome, ob.fuel);
  switch (ob.kind) {
    // A production failure is about the certificate as a whole: no point, and no
    // obligation to name.
    case "production-failure":
      return { searchOutcome: searched };
    case "source-refusal":
      return { summary: ob.reason, searchOutcome: searched };
    case "direct-obligation":
      return {
        summary: `The required subtype relation was not established: ${recordType(ob, ob.judgment.actual)} ≤ ${recordType(ob, ob.judgment.expected)}.`,
        searchOutcome: searched,
      };
    case "edge-coverage": {
      // The destination map acts after the result is pushed: target slot i takes
      // source slot mapping[i]. A null mapping selects the available context as
      // it is. Nothing here says which end is at fault; it says where the two
      // ends stop agreeing, which is all the record supports.
      const available = ob.transfer.available;
      const mapping = ob.transfer.target.mapping;
      const required = ob.destination.claim?.context ?? [];
      const names = bindingsOf(ob.destination.sourceMap, source);
      // An edge refused for facts its target requires: those facts and the
      // facts known on the edge.
      const facts = ob.edgeFacts === undefined ? undefined : edgeFactsText(ob.edgeFacts,
        spanText(ob.source.sourceMap, source, `node ${ob.source.label}`), (slot) => names[slot] || "slot " + slot, required.length,
        (slot) => isCell(ob, required[slot]));
      if (facts !== undefined) return { summary: facts, searchOutcome: searched };
      // The available labels target slot i takes; none where the mapping
      // names no source slot for it.
      const availableAt = (i: number): readonly number[] | undefined => {
        const at = mapping === null ? i : mapping[i];
        return at === undefined ? undefined : available[at];
      };
      const slot = required.findIndex((need: readonly number[], i: number) => !sameType(availableAt(i), need));
      if (slot >= 0) {
        const have = recordType(ob, availableAt(slot));
        const need = recordType(ob, required[slot]);
        const binding = names[slot] || "slot " + slot;
        if (need)
          return {
            summary: `The incoming claim for ${binding} is ${have}. The next point requires ${need}.`,
            searchOutcome: searched,
          };
      }
      if (requiresKnowledge(ob.destination.requiredKnowledge))
        return {
          summary: "The incoming claims do not establish the required current-content facts below.",
          searchOutcome: searched,
        };
      return { searchOutcome: searched };
    }
    case "node-typing":
    case "expression-claim": {
      const sourceMap: SourceMapEntry | null = ob.kind === "expression-claim" ? ob.sourceMap : ob.source.sourceMap;
      const q = ob.sequent;
      const names = bindingsOf(sourceMap, source);
      const binding = (slot: number) => names[slot] || "slot " + slot;
      const inContext = (slot: number) => Number.isInteger(slot) && slot >= 0 && slot < q.context.length;
      const term = q.term;
      // A return refused for its postcondition: its facts.
      const post = ob.kind === "node-typing" && ob.postcondition !== undefined
        ? postconditionText(ob.postcondition, binding, q.context.length) : undefined;
      if (post !== undefined) return { summary: post, searchOutcome: searched };
      if (term.kind === "var" && inContext(term.i)) {
        const slot = term.i;
        const required = recordType(ob, q.type);
        const role = sourceMap?.role;
        const isReturn = role === "return-contract" || role === "closure-result";
        return {
          summary: `The available claim for ${binding(slot)} is ${recordType(ob, q.context[slot])}. ${isReturn ? "This return" : "This obligation"} requires ${required}.`,
          searchOutcome: searched,
        };
      }
      if (term.kind === "nul" || term.kind === "undef" || term.kind === "tru" || term.kind === "fls")
        return { searchOutcome: searched };

      // Not a slot: name the term's form and the claims of the slots it reads
      // directly, which are what the rule for that form would use: a slot
      // that is a part of it, an element of a list of its parts, a part of a
      // part, or a part of its call code, in the order of the parts' names.
      const form = term.kind;
      const op = term.kind === "arith" ? ` ${term.op}` : "";
      const slots = new Set<number>();
      const slot = (t: Term): void => { if (t.kind === "var") slots.add(t.i); };
      for (const part of termParts(term)) {
        switch (part.k) {
          case "term":
            if (part.t.kind === "var") slots.add(part.t.i);
            else for (const inner of termParts(part.t)) if (inner.k === "term") slot(inner.t);
            break;
          case "terms": part.ts.forEach(slot); break;
          case "code": codeTerms(part.c).forEach(slot); break;
        }
      }
      const operands = [...slots].flatMap((s) =>
        inContext(s) ? [`${binding(s)}: ${recordType(ob, q.context[s])}`] : []);
      // A step whose preconditions do not all hold: those requirements and
      // the facts known over its operands, then its operands' claims.
      if (ob.kind === "node-typing" && ob.preconditions !== undefined)
        return {
          summary: `No rule derives this ${form}${op} at ${recordType(ob, q.type)}. ` +
            preconditionsText(ob.preconditions, binding, q.context.length) +
            (operands.length ? ` Its operands' claims: ${operands.join(", ")}.` : ""),
          searchOutcome: searched,
        };
      return {
        summary: `No rule derives this ${form}${op} at ${recordType(ob, q.type)}` +
          (operands.length ? ` from ${operands.join(", ")}.` : "."),
        searchOutcome: searched,
      };
    }
  }
}
