/* Reading the verifier's diagnostic record for display.
 *
 * A record describes an unsuccessful verification attempt: the assumptions that
 * were available and the conclusion that had to follow. It is explanatory
 * metadata, never proof evidence and never a judgement that a claim is false.
 * See docs/OBLIGATION-DIAGNOSTICS.md.
 */

import { isJsonList, type CallCode, type JsonRead, type JsonValue, type Term } from "./calculus.mts";
import surface from "./claim-text.mts";
import type { DiagnosticOutcome, HeapKnowledge, ObligationDiagnostic, SourceMapEntry } from "./diagnostic.mts";

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
// name, or the expression whose value it holds. Extraction guarantees one of the
// two for every binding and fails rather than emit a context it cannot describe,
// so a position should never reach a reader. The `slot N` fallback below is for
// a record that arrives without a source map at all; seeing one means the
// producer broke that invariant.
function bindingText(descriptor: Descriptor, source: string): string {
  if (descriptor.name) return descriptor.name;
  const span = descriptor.span;
  if (span === null) return "";
  return source
    .slice(span[0], span[1])
    .replace(/\s+/g, " ")
    .trim();
}

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
      return {
        summary: `No rule derives this ${form}${op} at ${recordType(ob, q.type)}` +
          (operands.length ? ` from ${operands.join(", ")}.` : "."),
        searchOutcome: searched,
      };
    }
  }
}
