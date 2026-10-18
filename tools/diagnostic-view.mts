/* Reading the verifier's diagnostic record for display.
 *
 * A record describes an unsuccessful verification attempt: the assumptions that
 * were available and the conclusion that had to follow. It is explanatory
 * metadata, never proof evidence and never a judgement that a claim is false.
 * See ../OBLIGATION-DIAGNOSTICS.md.
 */

import surface from "./claim-text.mts";
import type { DiagnosticOutcome, HeapKnowledge, ObligationDiagnostic, SourceMapEntry } from "./diagnostic.mts";

/* A record reaches `presentObligation` decoded: diagnostic.mts checks one field
 * by field and refuses what does not fit, so the shapes below are the ones that
 * arrive. The descriptors and label lists are the exception — they arrive as a
 * producer wrote them — so reading one narrows what arrived instead of assuming
 * it. `Array.isArray` alone would widen `unknown` to `any[]`, which is how
 * elements stop being checked; `isList` keeps them unknown. */
const isRecord = (v: unknown): v is Record<string, unknown> =>
  !!v && typeof v === "object";
const isList = (v: unknown): v is unknown[] => Array.isArray(v);

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
  types: unknown;
  names?: readonly (readonly [number, string])[];
}
function recordType(table: Table, labels: unknown): string {
  if (!isList(labels)) return "(no type recorded)";
  return surface.printType(surface.lift(table.types, labels, 3, table.names ?? [])).text;
}

/* ---------- source maps ---------- */
// A descriptor says how one context binding is named in the source: a binding
// name, or the expression whose value it holds. Extraction guarantees one of the
// two for every binding and fails rather than emit a context it cannot describe,
// so a position should never reach a reader. The `slot N` fallback below is for
// a record that arrives without a source map at all; seeing one means the
// producer broke that invariant.
function bindingText(descriptor: unknown, source: string): string {
  if (!isRecord(descriptor)) return "";
  if (descriptor.name) return String(descriptor.name);
  const span = descriptor.span;
  if (!isList(span) || typeof span[0] !== "number" || typeof span[1] !== "number")
    return "";
  return source
    .slice(span[0], span[1])
    .replace(/\s+/g, " ")
    .trim();
}

const bindingsOf = (map: { context?: unknown } | null, source: string): string[] =>
  (isList(map?.context) ? map.context : []).map((d) => bindingText(d, source));

/** Whether a node or edge end required any fact of the heap as it is. */
const requiresKnowledge = (knowledge: HeapKnowledge | null): boolean =>
  !!knowledge && knowledge.cells.length + knowledge.values.length + knowledge.links.length > 0;

const sameType = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b);

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
      const slot = required.findIndex((need, i) =>
        !sameType(mapping === null ? available[i] : available[mapping[i]], need));
      if (slot >= 0) {
        const have = recordType(ob, mapping === null ? available[slot] : available[mapping[slot]]);
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
      // directly, which are what the rule for that form would use: those
      // within three levels of the wire's nesting, where a constructor's
      // fields sit two levels below it, in the wire's order of their names.
      const form = term.kind;
      const op = term.kind === "arith" ? ` ${term.op}` : "";
      const slots = new Set<number>();
      const visitFields = (v: object, depth: number): void => {
        const entries: [string, unknown][] = Object.entries(v);
        const named = entries.filter(([k]) => k !== "kind").sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
        for (const [, x] of named) visit(x, depth);
      };
      const visit = (v: unknown, depth: number): void => {
        if (typeof v !== "object" || v === null || depth > 3) return;
        if (Array.isArray(v)) {
          const elements: unknown[] = v;
          for (const x of elements) visit(x, depth + 1);
          return;
        }
        if ("kind" in v) {
          if (v.kind === "var" && "i" in v && typeof v.i === "number") {
            slots.add(v.i);
            return;
          }
          if (depth + 1 <= 3) visitFields(v, depth + 2);
          return;
        }
        const values: unknown[] = Object.values(v);
        for (const x of values) visit(x, depth + 1);
      };
      visitFields(term, 1);
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
