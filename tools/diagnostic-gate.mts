import type { Node } from "typescript/unstable/ast";
import type { Gate } from "./fragment-parse.mts";
import type { Span } from "./span.mts";
import { abrupt } from "./fragment-statements.mts";
import { passToolFailure } from "./thrown.mts";

/** A refusal carries its source identity independently of its wording. */
export class GateRefusal extends Error {
  readonly pos: Span;
  constructor(message: string, pos: Span) {
    super(message);
    this.pos = pos;
  }
}

export type GateOccurrence = { pos: Span; region: Span; reason: string; recovery: string };

/** Gate state contains mutable containers and immutable compiler nodes.
 * Copy containers with their sharing preserved; compiler nodes stay in the
 * compiler's ownership. This copy is used only by diagnostic transactions. */
function copied(value: unknown, seen: Map<object, unknown>): unknown {
  if (!value || typeof value !== "object") return value;
  if ("getStart" in value && typeof value.getStart === "function") return value;
  if (seen.has(value)) return seen.get(value);
  if (value instanceof Map) {
    const result = new Map<unknown, unknown>();
    seen.set(value, result);
    for (const [key, item] of value) result.set(key, copied(item, seen));
    return result;
  }
  if (value instanceof Set) {
    const result = new Set<unknown>();
    seen.set(value, result);
    for (const item of value) result.add(copied(item, seen));
    return result;
  }
  if (Array.isArray(value)) {
    const result: unknown[] = [];
    seen.set(value, result);
    for (const item of value) result.push(copied(item, seen));
    return result;
  }
  if (Object.getPrototypeOf(value) !== Object.prototype) return value;
  const result: Record<string, unknown> = {};
  seen.set(value, result);
  for (const [key, item] of Object.entries(value)) result[key] = copied(item, seen);
  return result;
}

/** Copying preserves the input shape and the types of its fields. */
function copy<T>(value: T, seen: Map<object, unknown>): T {
  // asserted: copied preserves primitives, prototypes, keys and container shapes; only mutable container identities change
  return copied(value, seen) as T;
}

/** Recovery is installed only on a gate owned by the diagnostic parser.
 * A failed operation restores its entry state before substituting an opaque
 * region. The region's internal obligations remain explicitly unexamined. */
export function recoverGate(gate: Gate, occurrences: GateOccurrence[]): void {
  const attempt = <T,>(node: Node | undefined | null, recovery: string, run: () => T, fallback: () => T, region?: Span): T => {
    const snapshot = Object.getOwnPropertyDescriptors(gate);
    const seen = new Map<object, unknown>();
    for (const descriptor of Object.values(snapshot)) descriptor.value = copy(descriptor.value, seen);
    try {
      return run();
    } catch (error) {
      passToolFailure(error);
      if (!(error instanceof GateRefusal)) throw error;
      Object.defineProperties(gate, snapshot);
      occurrences.push({ pos: error.pos, region: region ?? (node ? gate.span(node) : [0, gate.file.end]),
        reason: error.message, recovery });
      return fallback();
    }
  };
  const expr = gate.expr.bind(gate);
  gate.expr = (node) => attempt(node, "opaque expression replaced by undefined", () => expr(node),
    () => ({ k: "lit", pos: gate.span(node), lit: { a: "undefined" } }));
  const stmt = gate.stmt.bind(gate);
  gate.stmt = (node) => attempt(node, "opaque statement omitted", () => stmt(node),
    () => ({ k: "block", pos: gate.span(node), label: null, body: [] }));
  const type = gate.typeOf.bind(gate);
  gate.typeOf = (node, at = null) => attempt(node ?? at, "opaque annotation replaced by unknown", () => type(node, at),
    () => ({ k: "atom", name: "unknown", span: node ? gate.span(node) : at ? gate.span(at) : [0, 0] }));
  const classStmt = gate.classStmt.bind(gate);
  gate.classStmt = (node) => attempt(node, "opaque class initialization omitted", () => classStmt(node),
    () => ({ k: "block", pos: gate.span(node), label: null, body: [] }));
  const hoisting = gate.hoisting.bind(gate);
  gate.hoisting = (node) => attempt(node, "opaque hoisting operation omitted", () => hoisting(node), () => []);
  const statements = gate.statements.bind(gate);
  gate.statements = (nodes) => attempt(nodes[0], "statement-list preparation bypassed; statements attempted independently",
    () => statements(nodes), () => {
      const end = nodes.findIndex(abrupt);
      return (end < 0 ? nodes : nodes.slice(0, end + 1)).flatMap(node => gate.hoisting(node));
    },
    [nodes[0] ? gate.span(nodes[0])[0] : 0, nodes.at(-1)?.end ?? 0]);

}
