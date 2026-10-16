/** Native program-graph syntax, matching ControlFlow.lean and its derived JSON
 * codec. A node is one term plus the continuation that follows it, and every
 * destination states its label and slot map, so the graph is explicit program
 * data the reader validates rather than structure it infers from terms. */
import { decodeTerm, fields, isTag, nat, type Tag, type Term } from "./calculus.mts";

export interface Target { label: number; mapping: number[] | null }
export type Continuation = "ret"
  | {bind: {next: Target}} | {effect: {next: Target}}
  | {branch: {yes: Target; no: Target}}
  | {branchBind: {yes: Target; no: Target}}
  | {tagBind: {test: Tag; yes: Target; no: Target}};
/** A node's handler is where a throw out of its expression goes, the thrown
 * value bound first; none lets the throw leave the program. */
export interface ProgramNode { expression: Term; continuation: Continuation; handler: Target | null }
function decodeTarget(value: unknown): Target {
  const t = fields(value,["label","mapping"]); nat(t.label);
  if (t.mapping !== null) {
    if (!Array.isArray(t.mapping)) throw Error("invalid slot mapping");
    t.mapping.forEach(nat);
  }
  // asserted: the decoder's result, checked field by field above
  return value as Target;
}
/** A continuation other than `ret`, checked field by field. */
function checkContinuation(continuation: unknown): void {
  if (!continuation || typeof continuation !== "object") throw Error("invalid continuation");
  const k = Object.keys(continuation)[0], outer = fields(continuation,[k]);
  switch (k) {
    case "bind": case "effect": decodeTarget(fields(outer[k],["next"]).next); break;
    case "branch": case "branchBind": case "tagBind": {
      const c = fields(outer[k], k === "tagBind" ? ["test","yes","no"] : ["yes","no"]);
      decodeTarget(c.yes); decodeTarget(c.no);
      if (k === "tagBind" && !isTag(c.test)) throw Error("invalid tag");
      break;
    }
    default: throw Error("unknown continuation");
  }
}
export function decodeNode(value: unknown): ProgramNode {
  const n = fields(value,["expression","continuation","handler"]); decodeTerm(n.expression);
  if (n.handler !== null) decodeTarget(n.handler);
  // A returning node has nothing else to check.
  if (n.continuation !== "ret") checkContinuation(n.continuation);
  // asserted: the decoder's result, checked field by field above
  return value as ProgramNode;
}
