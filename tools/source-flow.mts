/** Claim-independent execution graphs supplied by Lean to the producer. */
import type { Span } from "./span.mts";

interface FlowBinding { name: string; source: Span }
interface FlowHandler { target: number; scope: FlowBinding[]; binding: FlowBinding }
type FlowAction =
  | { kind: "end" }
  | { kind: "jump"; target: number }
  | { kind: "stmt"; statement: Span; next: number }
  | { kind: "declaration"; statement: Span; name: string; initializer: Span; mutable: boolean; next: number }
  | { kind: "branch"; statement: Span; yes: number; no: number }
  | { kind: "return"; statement: Span }
  | { kind: "returnSave"; statement: Span; binding: FlowBinding; next: number }
  | { kind: "returnHeld"; binding: FlowBinding }
  | { kind: "rethrow"; binding: FlowBinding }
  | { kind: "discardThrow"; binding: FlowBinding; next: number }
  | { kind: "iteratorStart"; statement: Span; binding: FlowBinding; next: number }
  | { kind: "iteratorStep"; statement: Span; binding: FlowBinding; element: FlowBinding; yes: number; no: number };
interface SavedValue { id: number; name: string; source: Span; role: string }
type ExecutionEffect =
  | { kind: "none" | "havoc" }
  | { kind: "cellWrite"; name: string; value: Span }
  | { kind: "cellUpdate"; name: string; source: Span };
type ExecutionReference =
  | { kind: "local"; name: string; source: Span }
  | { kind: "field"; source: Span; receiver: SavedValue; key: SavedValue | null };
export type ExecutionOperation =
  | { kind: "evaluate"; source: Span; effect: ExecutionEffect }
  | { kind: "methodRead"; source: Span; receiver: SavedValue; key: SavedValue | null; call: Span }
  | { kind: "invokeSaved"; source: Span; receiver: SavedValue; method: SavedValue }
  | { kind: "snapshotSpread"; source: Span; value: SavedValue; call: Span }
  | { kind: "snapshotObject"; source: Span; value: SavedValue }
  | { kind: "referenceRead"; source: Span; reference: ExecutionReference }
  | { kind: "referenceWrite"; source: Span; reference: ExecutionReference; value: SavedValue }
  | { kind: "updateSaved"; source: Span; reference: ExecutionReference; previous: SavedValue; rhs: SavedValue | null }
  | { kind: "positionRead"; source: Span; array: SavedValue; index: number }
  | { kind: "arrayRest"; source: Span; array: SavedValue; start: number; slice: boolean }
  | { kind: "emptyObject"; source: Span }
  | { kind: "addField"; source: Span; base: SavedValue; key: string | { symbol: number }; value: SavedValue; final: boolean }
  | { kind: "mergeObjects"; source: Span; left: SavedValue; right: SavedValue; final: boolean; assign: boolean };
export type ExecutionPlan =
  | { kind: "observe"; source: Span; evaluate: ExecutionPlan }
  | { kind: "atom"; source: Span; operation: ExecutionOperation }
  | { kind: "sequence"; source: Span; binding: SavedValue; evaluate: ExecutionPlan; next: ExecutionPlan }
  | { kind: "choose"; source: Span; condition: Span; test: "truthy" | "nullish" | "defined";
      binding: SavedValue; evaluate: ExecutionPlan; yes: ExecutionPlan; no: ExecutionPlan };
type BindingPlan =
  | { kind: "finish" }
  | { kind: "evaluate"; value: SavedValue; plan: ExecutionPlan; next: BindingPlan }
  | { kind: "defaultValue"; value: SavedValue; result: SavedValue; fallback: ExecutionPlan; next: BindingPlan }
  | { kind: "bind"; name: string; origin: Span; value: SavedValue; next: BindingPlan }
  | { kind: "input"; name: string; index: number; value: SavedValue; next: BindingPlan }
  | { kind: "readField"; source: Span; receiver: SavedValue; field: string; value: SavedValue; next: BindingPlan }
  | { kind: "readPosition"; source: Span; array: SavedValue; index: number; value: SavedValue; next: BindingPlan }
  | { kind: "objectRest"; source: Span; receiver: SavedValue; drop: string[]; value: SavedValue; next: BindingPlan }
  | { kind: "arrayRest"; source: Span; array: SavedValue; start: number; slice: boolean; value: SavedValue; next: BindingPlan };
interface SourceExecution { source: Span; plan: ExecutionPlan }
interface FlowNode {
  id: number;
  point: string;
  source: Span;
  scope: FlowBinding[];
  handler: FlowHandler | null;
  action: FlowAction;
  executions: SourceExecution[];
  bindingPlan: BindingPlan | null;
}
/** `cells`: the body's mutable bindings held in cells, a `let` named with its
 * declaring statement, an assigned parameter with the owner; every other
 * mutable binding is a slot of the body's activation. */
interface FlowGraph { owner: Span; bodySpans: Span[]; entry: number; cells: FlowBinding[]; prologue: BindingPlan | null; nodes: FlowNode[] }
type FlowDocument = FlowGraph[];

const invalid = (what: string): never => { throw Error(`invalid control-flow document: ${what}`); };
const object = (value: unknown): Record<string, unknown> => {
  if (!value || typeof value !== "object" || Array.isArray(value)) return invalid("object required");
  return Object.fromEntries(Object.entries(value));
};
const exact = (value: Record<string, unknown>, fields: readonly string[]): void => {
  if (Object.keys(value).length !== fields.length || fields.some((field) => !Object.hasOwn(value, field)))
    invalid("unexpected or missing fields");
};
const array = (value: unknown): unknown[] => Array.isArray(value) ? value : invalid("array required");
const natural = (value: unknown): number =>
  typeof value === "number" && Number.isSafeInteger(value) && value >= 0 ? value : invalid("natural number required");
const span = (value: unknown): void => {
  const xs = array(value);
  if (xs.length !== 2 || natural(xs[1]) < natural(xs[0])) invalid("source span");
};
const text = (value: unknown): void => { if (typeof value !== "string") invalid("string required"); };
const binding = (value: unknown): void => {
  const b = object(value); exact(b, ["name", "source"]);
  if (typeof b.name !== "string") invalid("binding name");
  span(b.source);
};
const scope = (value: unknown): void => { array(value).forEach(binding); };

const saved = (value: unknown): void => {
  const b = object(value); exact(b, ["id", "name", "source", "role"]);
  natural(b.id); span(b.source);
  if (typeof b.name !== "string" || typeof b.role !== "string") invalid("saved value");
};
const executionEffect = (value: unknown): void => {
  const e = object(value);
  switch (e.kind) {
    case "none": case "havoc": exact(e, ["kind"]); break;
    case "cellWrite": exact(e, ["kind", "name", "value"]); span(e.value);
      if (typeof e.name !== "string") invalid("cell write name"); break;
    case "cellUpdate": exact(e, ["kind", "name", "source"]); span(e.source);
      if (typeof e.name !== "string") invalid("cell update name"); break;
    default: invalid("unknown execution effect");
  }
};
const reference = (value: unknown): void => {
  const ref = object(value); span(ref.source);
  switch (ref.kind) {
    case "local": exact(ref, ["kind", "name", "source"]);
      if (typeof ref.name !== "string") invalid("local reference name"); break;
    case "field": exact(ref, ["kind", "source", "receiver", "key"]);
      saved(ref.receiver); if (ref.key !== null) saved(ref.key); break;
    default: invalid("unknown execution reference");
  }
};
const operation = (value: unknown): void => {
  const op = object(value); span(op.source);
  switch (op.kind) {
    case "evaluate": exact(op, ["kind", "source", "effect"]); executionEffect(op.effect); break;
    case "methodRead": exact(op, ["kind", "source", "receiver", "key", "call"]);
      saved(op.receiver); if (op.key !== null) saved(op.key); span(op.call); break;
    case "invokeSaved": exact(op, ["kind", "source", "receiver", "method"]); saved(op.receiver); saved(op.method); break;
    case "snapshotSpread": exact(op, ["kind", "source", "value", "call"]); saved(op.value); span(op.call); break;
    case "snapshotObject": exact(op, ["kind", "source", "value"]); saved(op.value); break;
    case "referenceRead": exact(op, ["kind", "source", "reference"]); reference(op.reference); break;
    case "referenceWrite": exact(op, ["kind", "source", "reference", "value"]); reference(op.reference); saved(op.value); break;
    case "updateSaved": exact(op, ["kind", "source", "reference", "previous", "rhs"]);
      reference(op.reference); saved(op.previous); if (op.rhs !== null) saved(op.rhs); break;
    case "positionRead": exact(op, ["kind", "source", "array", "index"]); saved(op.array); natural(op.index); break;
    case "arrayRest": exact(op, ["kind", "source", "array", "start", "slice"]);
      saved(op.array); natural(op.start); if (typeof op.slice !== "boolean") invalid("array rest mode"); break;
    case "emptyObject": exact(op, ["kind", "source"]); break;
    case "addField": exact(op, ["kind", "source", "base", "key", "value", "final"]); saved(op.base); saved(op.value);
      if (typeof op.final !== "boolean") invalid("object completion");
      if (typeof op.key !== "string") { const key = object(op.key); exact(key, ["symbol"]); natural(key.symbol); } break;
    case "mergeObjects": exact(op, ["kind", "source", "left", "right", "final", "assign"]); saved(op.left); saved(op.right);
      if (typeof op.final !== "boolean" || typeof op.assign !== "boolean") invalid("object merge mode"); break;
    default: invalid("unknown execution operation");
  }
};
const plan = (value: unknown): void => {
  const p = object(value); span(p.source);
  switch (p.kind) {
    case "observe": exact(p, ["kind", "source", "evaluate"]); plan(p.evaluate); break;
    case "atom": exact(p, ["kind", "source", "operation"]); operation(p.operation); break;
    case "sequence": exact(p, ["kind", "source", "binding", "evaluate", "next"]);
      saved(p.binding); plan(p.evaluate); plan(p.next); break;
    case "choose": exact(p, ["kind", "source", "condition", "test", "binding", "evaluate", "yes", "no"]);
      span(p.condition); if (p.test !== "truthy" && p.test !== "nullish" && p.test !== "defined") invalid("branch test");
      saved(p.binding); plan(p.evaluate); plan(p.yes); plan(p.no); break;
    default: invalid("unknown execution plan");
  }
};

/** Require the exact current wire shape and graph-local edge associations. */
const bindingPlan = (value: unknown): void => {
  const b = object(value);
  if (b.kind === "finish") { exact(b, ["kind"]); return; }
  saved(b.value);
  switch (b.kind) {
    case "evaluate": exact(b, ["kind", "value", "plan", "next"]); plan(b.plan); bindingPlan(b.next); break;
    case "defaultValue": exact(b, ["kind", "value", "result", "fallback", "next"]);
      saved(b.result); plan(b.fallback); bindingPlan(b.next); break;
    case "bind": exact(b, ["kind", "name", "origin", "value", "next"]); text(b.name); span(b.origin); bindingPlan(b.next); break;
    case "input": exact(b, ["kind", "name", "index", "value", "next"]); text(b.name); natural(b.index); bindingPlan(b.next); break;
    case "readField": exact(b, ["kind", "source", "receiver", "field", "value", "next"]);
      span(b.source); saved(b.receiver); text(b.field); bindingPlan(b.next); break;
    case "readPosition": exact(b, ["kind", "source", "array", "index", "value", "next"]);
      span(b.source); saved(b.array); natural(b.index); bindingPlan(b.next); break;
    case "objectRest": exact(b, ["kind", "source", "receiver", "drop", "value", "next"]);
      span(b.source); saved(b.receiver); array(b.drop).forEach(text); bindingPlan(b.next); break;
    case "arrayRest": exact(b, ["kind", "source", "array", "start", "slice", "value", "next"]);
      span(b.source); saved(b.array); natural(b.start);
      if (typeof b.slice !== "boolean") invalid("binding array rest mode"); bindingPlan(b.next); break;
    default: invalid("unknown binding plan");
  }
};

export function decodeFlowDocument(value: unknown): FlowDocument {
  const owners = new Set<string>();
  for (const raw of array(value)) {
    const graph = object(raw); exact(graph, ["owner", "bodySpans", "entry", "cells", "prologue", "nodes"]);
    span(graph.owner); if (graph.prologue !== null) bindingPlan(graph.prologue); array(graph.bodySpans).forEach(span);
    scope(graph.cells);
    const owner = array(graph.owner).join(":");
    if (owners.has(owner)) invalid("duplicate graph owner");
    owners.add(owner);
    const nodes = array(graph.nodes);
    const edge = (target: unknown): void => { if (natural(target) >= nodes.length) invalid("edge names a missing node"); };
    edge(graph.entry);
    nodes.forEach((rawNode, id) => {
      const node = object(rawNode); exact(node, ["id", "point", "source", "scope", "handler", "action", "executions", "bindingPlan"]);
      if (natural(node.id) !== id || node.point !== `${owner}:${id}`) invalid("node identity");
      span(node.source); scope(node.scope); if (node.bindingPlan !== null) bindingPlan(node.bindingPlan);
      for (const rawExecution of array(node.executions)) {
        const execution = object(rawExecution); exact(execution, ["source", "plan"]);
        span(execution.source); plan(execution.plan);
      }
      if (node.handler !== null) {
        const h = object(node.handler); exact(h, ["target", "scope", "binding"]);
        edge(h.target); scope(h.scope); binding(h.binding);
      }
      const action = object(node.action);
      switch (action.kind) {
        case "end": exact(action, ["kind"]); break;
        case "jump": exact(action, ["kind", "target"]); edge(action.target); break;
        case "stmt": exact(action, ["kind", "statement", "next"]); span(action.statement); edge(action.next); break;
        case "declaration": exact(action, ["kind", "statement", "name", "initializer", "mutable", "next"]);
          span(action.statement); text(action.name); span(action.initializer);
          if (typeof action.mutable !== "boolean") invalid("declaration storage mode"); edge(action.next); break;
        case "branch": exact(action, ["kind", "statement", "yes", "no"]); span(action.statement); edge(action.yes); edge(action.no); break;
        case "return": exact(action, ["kind", "statement"]); span(action.statement); break;
        case "returnSave":
        case "iteratorStart": exact(action, ["kind", "statement", "binding", "next"]); span(action.statement); binding(action.binding); edge(action.next); break;
        case "returnHeld":
        case "rethrow": exact(action, ["kind", "binding"]); binding(action.binding); break;
        case "discardThrow": exact(action, ["kind", "binding", "next"]); binding(action.binding); edge(action.next); break;
        case "iteratorStep": exact(action, ["kind", "statement", "binding", "element", "yes", "no"]); span(action.statement); binding(action.binding); binding(action.element); edge(action.yes); edge(action.no); break;
        default: invalid("unknown action kind");
      }
    });
  }
  return value as FlowDocument; // asserted: every field, action variant, node identity and edge target is checked above.
}
