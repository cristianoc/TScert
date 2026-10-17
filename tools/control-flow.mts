/** Native program-graph syntax, matching ControlFlow.lean and its derived JSON
 * codec. A node is one term plus the continuation that follows it, and every
 * destination states its label and slot map, so the graph is explicit program
 * data the reader validates rather than structure it infers from terms. As in
 * calculus.mts, the wire writes a continuation as an object with one key, its
 * constructor's name, and the decoder builds a value naming it in `kind`. */
import { constructorOf, decodeTag, decodeTerm, fields, nat, type Tag, type Term } from "./calculus.mts";

export interface Target { label: number; mapping: number[] | null }
export type Continuation =
  | { kind: "ret" }
  | { kind: "bind"; next: Target }
  | { kind: "effect"; next: Target }
  | { kind: "branch"; yes: Target; no: Target }
  | { kind: "branchBind"; yes: Target; no: Target }
  | { kind: "tagBind"; test: Tag; yes: Target; no: Target };
/** A node's handler is where a throw out of its expression goes, the thrown
 * value bound first; none lets the throw leave the program. */
export interface ProgramNode { expression: Term; continuation: Continuation; handler: Target | null }
function decodeTarget(value: unknown): Target {
  const t = fields(value, ["label", "mapping"]);
  const label = nat(t.label);
  if (t.mapping === null) return { label, mapping: null };
  if (!Array.isArray(t.mapping)) throw Error("invalid slot mapping");
  return { label, mapping: t.mapping.map(nat) };
}
function decodeContinuation(continuation: unknown): Continuation {
  if (continuation === "ret") return { kind: "ret" };
  if (!continuation || typeof continuation !== "object") throw Error("invalid continuation");
  const { key, value } = constructorOf(continuation);
  switch (key) {
    case "bind": return { kind: "bind", next: decodeTarget(fields(value, ["next"]).next) };
    case "effect": return { kind: "effect", next: decodeTarget(fields(value, ["next"]).next) };
    case "branch": {
      const c = fields(value, ["yes", "no"]);
      return { kind: "branch", yes: decodeTarget(c.yes), no: decodeTarget(c.no) };
    }
    case "branchBind": {
      const c = fields(value, ["yes", "no"]);
      return { kind: "branchBind", yes: decodeTarget(c.yes), no: decodeTarget(c.no) };
    }
    case "tagBind": {
      const c = fields(value, ["test", "yes", "no"]);
      const yes = decodeTarget(c.yes), no = decodeTarget(c.no);
      return { kind: "tagBind", test: decodeTag(c.test), yes, no };
    }
    default: throw Error("unknown continuation");
  }
}
export function decodeNode(value: unknown): ProgramNode {
  const n = fields(value, ["expression", "continuation", "handler"]);
  const expression = decodeTerm(n.expression);
  const handler = n.handler === null ? null : decodeTarget(n.handler);
  return { expression, continuation: decodeContinuation(n.continuation), handler };
}
