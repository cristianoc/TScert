/** The execution graphs Lean lowers a fragment's functions to (`verifier --lower-control-flow`). */
import { hasExactly, nat, type Json } from "./calculus.mts";
import type { Span } from "./span.mts";
import { requireWellFormed } from "./wire-strings.mts";

interface FlowBinding {
  name: string;
  source: Span;
}
interface EarlyBinding {
  statement: Span;
  name: string;
  initializer: Span;
  mutable: boolean;
}
interface FlowHandler {
  target: number;
  scope: FlowBinding[];
  binding: FlowBinding;
}
type FlowAction =
  | { kind: "end" }
  | { kind: "jump"; target: number }
  | { kind: "stmt"; statement: Span; next: number }
  | {
      kind: "declaration";
      statement: Span;
      name: string;
      initializer: Span;
      mutable: boolean;
      early: boolean;
      next: number;
    }
  /* The entry of a statement list declaring early bindings: their cells,
     holding the uninitialized marker, from here on. */
  | { kind: "early"; bindings: EarlyBinding[]; next: number }
  | { kind: "branch"; statement: Span; yes: number; no: number }
  | { kind: "return"; statement: Span }
  | { kind: "returnSave"; statement: Span; binding: FlowBinding; next: number }
  | { kind: "returnHeld"; binding: FlowBinding }
  | { kind: "rethrow"; binding: FlowBinding }
  | { kind: "discardThrow"; binding: FlowBinding; next: number }
  | {
      kind: "iteratorStart";
      statement: Span;
      binding: FlowBinding;
      next: number;
    }
  | {
      kind: "iteratorStep";
      statement: Span;
      binding: FlowBinding;
      element: FlowBinding;
      yes: number;
      no: number;
    };
interface SavedValue {
  id: number;
  name: string;
  source: Span;
  role: string;
}
type ExecutionEffect =
  | { kind: "none" | "havoc" }
  | { kind: "cellWrite"; name: string; value: Span }
  | { kind: "cellUpdate"; name: string; source: Span };
type ExecutionReference =
  | { kind: "local"; name: string; source: Span }
  | {
      kind: "field";
      source: Span;
      receiver: SavedValue;
      key: SavedValue | null;
    };
type ExecutionResult =
  | { kind: "unknown" }
  | { kind: "boolean"; value: boolean }
  | { kind: "saved" | "negated"; name: string };
export type ExecutionOperation =
  | {
      kind: "evaluate";
      source: Span;
      effect: ExecutionEffect;
      result: ExecutionResult;
    }
  | {
      kind: "methodRead";
      source: Span;
      receiver: SavedValue;
      key: SavedValue | null;
      call: Span;
    }
  | {
      kind: "invokeSaved";
      source: Span;
      receiver: SavedValue;
      method: SavedValue;
    }
  | { kind: "snapshotSpread"; source: Span; value: SavedValue; call: Span }
  | { kind: "snapshotObject"; source: Span; value: SavedValue }
  | { kind: "referenceRead"; source: Span; reference: ExecutionReference }
  | {
      kind: "referenceWrite";
      source: Span;
      reference: ExecutionReference;
      value: SavedValue;
    }
  | {
      kind: "updateSaved";
      source: Span;
      reference: ExecutionReference;
      previous: SavedValue;
      rhs: SavedValue | null;
    }
  | { kind: "positionRead"; source: Span; array: SavedValue; index: number }
  | {
      kind: "arrayRest";
      source: Span;
      array: SavedValue;
      start: number;
      slice: boolean;
    }
  | { kind: "emptyObject"; source: Span }
  | {
      kind: "addField";
      source: Span;
      base: SavedValue;
      key: string | { symbol: number };
      value: SavedValue;
      final: boolean;
    }
  | {
      kind: "mergeObjects";
      source: Span;
      left: SavedValue;
      right: SavedValue;
      final: boolean;
      assign: boolean;
    }
  | { kind: "outcome"; source: Span; truth: boolean };
export type ExecutionPlan =
  | { kind: "observe"; source: Span; evaluate: ExecutionPlan }
  | { kind: "atom"; source: Span; operation: ExecutionOperation }
  | {
      kind: "sequence";
      source: Span;
      binding: SavedValue;
      evaluate: ExecutionPlan;
      next: ExecutionPlan;
    }
  | {
      kind: "choose";
      source: Span;
      condition: Span;
      test: "truthy" | "nullish" | "defined";
      binding: SavedValue;
      evaluate: ExecutionPlan;
      yes: ExecutionPlan;
      no: ExecutionPlan;
    };
type BindingPlan =
  | { kind: "finish" }
  | {
      kind: "evaluate";
      value: SavedValue;
      plan: ExecutionPlan;
      next: BindingPlan;
    }
  | {
      kind: "defaultValue";
      value: SavedValue;
      result: SavedValue;
      fallback: ExecutionPlan;
      next: BindingPlan;
    }
  | {
      kind: "bind";
      name: string;
      origin: Span;
      value: SavedValue;
      next: BindingPlan;
    }
  | {
      kind: "input";
      name: string;
      index: number;
      value: SavedValue;
      next: BindingPlan;
    }
  | {
      kind: "readField";
      source: Span;
      receiver: SavedValue;
      field: string;
      value: SavedValue;
      next: BindingPlan;
    }
  | {
      kind: "readPosition";
      source: Span;
      array: SavedValue;
      index: number;
      value: SavedValue;
      next: BindingPlan;
    }
  | {
      kind: "objectRest";
      source: Span;
      receiver: SavedValue;
      drop: string[];
      value: SavedValue;
      next: BindingPlan;
    }
  | {
      kind: "arrayRest";
      source: Span;
      array: SavedValue;
      start: number;
      slice: boolean;
      value: SavedValue;
      next: BindingPlan;
    };
interface SourceExecution {
  source: Span;
  plan: ExecutionPlan;
}
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
interface FlowGraph {
  owner: Span;
  bodySpans: Span[];
  moduleReads: string[];
  entry: number;
  cells: FlowBinding[];
  prologue: BindingPlan | null;
  nodes: FlowNode[];
}
type FlowDocument = FlowGraph[];

const invalid: (what: string) => never = (what) => {
  throw Error(`invalid control-flow document: ${what}`);
};
const object = (value: unknown): Record<string, unknown> => {
  if (!value || typeof value !== "object" || Array.isArray(value))
    return invalid("object required");
  const entries: [string, unknown][] = Object.entries(value);
  return Object.fromEntries(entries);
};
const exact = (
  value: Record<string, unknown>,
  fields: readonly string[],
): void => {
  if (!hasExactly(value, fields)) invalid("unexpected or missing fields");
};
const array = (value: unknown): unknown[] =>
  Array.isArray(value) ? value : invalid("array required");
const span = (value: unknown): Span => {
  const xs = array(value);
  if (xs.length !== 2) invalid("source span");
  const end = nat(xs[1]);
  const start = nat(xs[0]);
  if (end < start) invalid("source span");
  return [start, end];
};
const text = (value: unknown): string => {
  if (typeof value !== "string") return invalid("string required");
  return value;
};
const bindingOf = (value: unknown): FlowBinding => {
  const b = object(value);
  exact(b, ["name", "source"]);
  if (typeof b.name !== "string") invalid("binding name");
  const name = b.name;
  const source = span(b.source);
  return { name, source };
};
const scope = (value: unknown): FlowBinding[] => array(value).map(bindingOf);

const saved = (value: unknown): SavedValue => {
  const b = object(value);
  exact(b, ["id", "name", "source", "role"]);
  const id = nat(b.id);
  const source = span(b.source);
  if (typeof b.name !== "string" || typeof b.role !== "string")
    invalid("saved value");
  return { id, source, name: b.name, role: b.role };
};
const executionEffect = (value: unknown): ExecutionEffect => {
  const e = object(value);
  switch (e.kind) {
    case "none":
    case "havoc": {
      exact(e, ["kind"]);
      return { kind: e.kind };
    }
    case "cellWrite": {
      exact(e, ["kind", "name", "value"]);
      const value = span(e.value);
      if (typeof e.name !== "string") invalid("cell write name");
      return { kind: e.kind, name: e.name, value };
    }
    case "cellUpdate": {
      exact(e, ["kind", "name", "source"]);
      const source = span(e.source);
      if (typeof e.name !== "string") invalid("cell update name");
      return { kind: e.kind, name: e.name, source };
    }
    default:
      invalid("unknown execution effect");
  }
};
const referenceOf = (value: unknown): ExecutionReference => {
  const ref = object(value);
  const source = span(ref.source);
  switch (ref.kind) {
    case "local": {
      exact(ref, ["kind", "name", "source"]);
      if (typeof ref.name !== "string") invalid("local reference name");
      return { kind: ref.kind, name: ref.name, source };
    }
    case "field": {
      exact(ref, ["kind", "source", "receiver", "key"]);
      const receiver = saved(ref.receiver);
      const key = ref.key === null ? null : saved(ref.key);
      return { kind: ref.kind, source, receiver, key };
    }
    default:
      invalid("unknown execution reference");
  }
};
const executionResult = (value: unknown): ExecutionResult => {
  const r = object(value);
  switch (r.kind) {
    case "unknown": {
      exact(r, ["kind"]);
      return { kind: r.kind };
    }
    case "boolean": {
      exact(r, ["kind", "value"]);
      if (typeof r.value !== "boolean") invalid("Boolean execution result");
      return { kind: r.kind, value: r.value };
    }
    case "saved":
    case "negated": {
      exact(r, ["kind", "name"]);
      if (typeof r.name !== "string") invalid("saved execution result");
      return { kind: r.kind, name: r.name };
    }
    default:
      invalid("unknown execution result");
  }
};
const operationOf = (value: unknown): ExecutionOperation => {
  const op = object(value);
  const source = span(op.source);
  switch (op.kind) {
    case "evaluate": {
      exact(op, ["kind", "source", "effect", "result"]);
      const result = executionResult(op.result);
      const effect = executionEffect(op.effect);
      return { kind: op.kind, source, effect, result };
    }
    case "methodRead": {
      exact(op, ["kind", "source", "receiver", "key", "call"]);
      const receiver = saved(op.receiver);
      const key = op.key === null ? null : saved(op.key);
      const call = span(op.call);
      return { kind: op.kind, source, receiver, key, call };
    }
    case "invokeSaved": {
      exact(op, ["kind", "source", "receiver", "method"]);
      const receiver = saved(op.receiver);
      const method = saved(op.method);
      return { kind: op.kind, source, receiver, method };
    }
    case "snapshotSpread": {
      exact(op, ["kind", "source", "value", "call"]);
      const value = saved(op.value);
      const call = span(op.call);
      return { kind: op.kind, source, value, call };
    }
    case "snapshotObject": {
      exact(op, ["kind", "source", "value"]);
      const value = saved(op.value);
      return { kind: op.kind, source, value };
    }
    case "referenceRead": {
      exact(op, ["kind", "source", "reference"]);
      const reference = referenceOf(op.reference);
      return { kind: op.kind, source, reference };
    }
    case "referenceWrite": {
      exact(op, ["kind", "source", "reference", "value"]);
      const reference = referenceOf(op.reference);
      const value = saved(op.value);
      return { kind: op.kind, source, reference, value };
    }
    case "updateSaved": {
      exact(op, ["kind", "source", "reference", "previous", "rhs"]);
      const reference = referenceOf(op.reference);
      const previous = saved(op.previous);
      const rhs = op.rhs === null ? null : saved(op.rhs);
      return { kind: op.kind, source, reference, previous, rhs };
    }
    case "positionRead": {
      exact(op, ["kind", "source", "array", "index"]);
      const array = saved(op.array);
      const index = nat(op.index);
      return { kind: op.kind, source, array, index };
    }
    case "arrayRest": {
      exact(op, ["kind", "source", "array", "start", "slice"]);
      const array = saved(op.array);
      const start = nat(op.start);
      if (typeof op.slice !== "boolean") invalid("array rest mode");
      return { kind: op.kind, source, array, start, slice: op.slice };
    }
    case "emptyObject": {
      exact(op, ["kind", "source"]);
      return { kind: op.kind, source };
    }
    case "addField": {
      exact(op, ["kind", "source", "base", "key", "value", "final"]);
      const base = saved(op.base);
      const value = saved(op.value);
      if (typeof op.final !== "boolean") invalid("object completion");
      let key: string | { symbol: number };
      if (typeof op.key !== "string") {
        const symbolKey = object(op.key);
        exact(symbolKey, ["symbol"]);
        key = { symbol: nat(symbolKey.symbol) };
      } else key = op.key;
      return { kind: op.kind, source, base, key, value, final: op.final };
    }
    case "mergeObjects": {
      exact(op, ["kind", "source", "left", "right", "final", "assign"]);
      const left = saved(op.left);
      const right = saved(op.right);
      if (typeof op.final !== "boolean" || typeof op.assign !== "boolean")
        invalid("object merge mode");
      return {
        kind: op.kind,
        source,
        left,
        right,
        final: op.final,
        assign: op.assign,
      };
    }
    case "outcome": {
      exact(op, ["kind", "source", "truth"]);
      if (typeof op.truth !== "boolean") invalid("condition outcome");
      return { kind: op.kind, source, truth: op.truth };
    }
    default:
      invalid("unknown execution operation");
  }
};
const planOf = (value: unknown): ExecutionPlan => {
  const p = object(value);
  const source = span(p.source);
  switch (p.kind) {
    case "observe": {
      exact(p, ["kind", "source", "evaluate"]);
      const evaluate = planOf(p.evaluate);
      return { kind: p.kind, source, evaluate };
    }
    case "atom": {
      exact(p, ["kind", "source", "operation"]);
      const operation = operationOf(p.operation);
      return { kind: p.kind, source, operation };
    }
    case "sequence": {
      exact(p, ["kind", "source", "binding", "evaluate", "next"]);
      const binding = saved(p.binding);
      const evaluate = planOf(p.evaluate);
      const next = planOf(p.next);
      return { kind: p.kind, source, binding, evaluate, next };
    }
    case "choose": {
      exact(p, [
        "kind",
        "source",
        "condition",
        "test",
        "binding",
        "evaluate",
        "yes",
        "no",
      ]);
      const condition = span(p.condition);
      if (p.test !== "truthy" && p.test !== "nullish" && p.test !== "defined")
        invalid("branch test");
      const binding = saved(p.binding);
      const evaluate = planOf(p.evaluate);
      const yes = planOf(p.yes);
      const no = planOf(p.no);
      return {
        kind: p.kind,
        source,
        condition,
        test: p.test,
        binding,
        evaluate,
        yes,
        no,
      };
    }
    default:
      invalid("unknown execution plan");
  }
};
const bindingPlan = (value: unknown): BindingPlan => {
  const b = object(value);
  if (b.kind === "finish") {
    exact(b, ["kind"]);
    return { kind: "finish" };
  }
  const decodedValue = saved(b.value);
  switch (b.kind) {
    case "evaluate": {
      exact(b, ["kind", "value", "plan", "next"]);
      const plan = planOf(b.plan);
      const next = bindingPlan(b.next);
      return { kind: b.kind, value: decodedValue, plan, next };
    }
    case "defaultValue": {
      exact(b, ["kind", "value", "result", "fallback", "next"]);
      const result = saved(b.result);
      const fallback = planOf(b.fallback);
      const next = bindingPlan(b.next);
      return { kind: b.kind, value: decodedValue, result, fallback, next };
    }
    case "bind": {
      exact(b, ["kind", "name", "origin", "value", "next"]);
      const name = text(b.name);
      const origin = span(b.origin);
      const next = bindingPlan(b.next);
      return { kind: b.kind, name, origin, value: decodedValue, next };
    }
    case "input": {
      exact(b, ["kind", "name", "index", "value", "next"]);
      const name = text(b.name);
      const index = nat(b.index);
      const next = bindingPlan(b.next);
      return { kind: b.kind, name, index, value: decodedValue, next };
    }
    case "readField": {
      exact(b, ["kind", "source", "receiver", "field", "value", "next"]);
      const source = span(b.source);
      const receiver = saved(b.receiver);
      const field = text(b.field);
      const next = bindingPlan(b.next);
      return {
        kind: b.kind,
        source,
        receiver,
        field,
        value: decodedValue,
        next,
      };
    }
    case "readPosition": {
      exact(b, ["kind", "source", "array", "index", "value", "next"]);
      const source = span(b.source);
      const array = saved(b.array);
      const index = nat(b.index);
      const next = bindingPlan(b.next);
      return { kind: b.kind, source, array, index, value: decodedValue, next };
    }
    case "objectRest": {
      exact(b, ["kind", "source", "receiver", "drop", "value", "next"]);
      const source = span(b.source);
      const receiver = saved(b.receiver);
      const drop = array(b.drop).map(text);
      const next = bindingPlan(b.next);
      return {
        kind: b.kind,
        source,
        receiver,
        drop,
        value: decodedValue,
        next,
      };
    }
    case "arrayRest": {
      exact(b, ["kind", "source", "array", "start", "slice", "value", "next"]);
      const source = span(b.source);
      const array = saved(b.array);
      const start = nat(b.start);
      if (typeof b.slice !== "boolean") invalid("binding array rest mode");
      const next = bindingPlan(b.next);
      return {
        kind: b.kind,
        source,
        array,
        start,
        slice: b.slice,
        value: decodedValue,
        next,
      };
    }
    default:
      invalid("unknown binding plan");
  }
};

const flowAction = (
  value: unknown,
  edge: (target: unknown) => number,
): FlowAction => {
  const action = object(value);
  switch (action.kind) {
    case "end": {
      exact(action, ["kind"]);
      return { kind: action.kind };
    }
    case "jump": {
      exact(action, ["kind", "target"]);
      const target = edge(action.target);
      return { kind: action.kind, target };
    }
    case "stmt": {
      exact(action, ["kind", "statement", "next"]);
      const statement = span(action.statement);
      const next = edge(action.next);
      return { kind: action.kind, statement, next };
    }
    case "declaration": {
      exact(action, [
        "kind",
        "statement",
        "name",
        "initializer",
        "mutable",
        "early",
        "next",
      ]);
      const statement = span(action.statement);
      const name = text(action.name);
      const initializer = span(action.initializer);
      if (typeof action.mutable !== "boolean")
        invalid("declaration storage mode");
      if (typeof action.early !== "boolean")
        invalid("declaration's early flag");
      const next = edge(action.next);
      return {
        kind: action.kind,
        statement,
        name,
        initializer,
        mutable: action.mutable,
        early: action.early,
        next,
      };
    }
    case "early": {
      exact(action, ["kind", "bindings", "next"]);
      const bindings = array(action.bindings).map((b): EarlyBinding => {
        const e = object(b);
        exact(e, ["statement", "name", "initializer", "mutable"]);
        const statement = span(e.statement);
        const name = text(e.name);
        const initializer = span(e.initializer);
        if (typeof e.mutable !== "boolean")
          invalid("early binding's storage mode");
        return { statement, name, initializer, mutable: e.mutable };
      });
      const next = edge(action.next);
      return { kind: action.kind, bindings, next };
    }
    case "branch": {
      exact(action, ["kind", "statement", "yes", "no"]);
      const statement = span(action.statement);
      const yes = edge(action.yes);
      const no = edge(action.no);
      return { kind: action.kind, statement, yes, no };
    }
    case "return": {
      exact(action, ["kind", "statement"]);
      const statement = span(action.statement);
      return { kind: action.kind, statement };
    }
    case "returnSave":
    case "iteratorStart": {
      exact(action, ["kind", "statement", "binding", "next"]);
      const statement = span(action.statement);
      const binding = bindingOf(action.binding);
      const next = edge(action.next);
      return { kind: action.kind, statement, binding, next };
    }
    case "returnHeld":
    case "rethrow": {
      exact(action, ["kind", "binding"]);
      const binding = bindingOf(action.binding);
      return { kind: action.kind, binding };
    }
    case "discardThrow": {
      exact(action, ["kind", "binding", "next"]);
      const binding = bindingOf(action.binding);
      const next = edge(action.next);
      return { kind: action.kind, binding, next };
    }
    case "iteratorStep": {
      exact(action, ["kind", "statement", "binding", "element", "yes", "no"]);
      const statement = span(action.statement);
      const binding = bindingOf(action.binding);
      const element = bindingOf(action.element);
      const yes = edge(action.yes);
      const no = edge(action.no);
      return { kind: action.kind, statement, binding, element, yes, no };
    }
    default:
      invalid("unknown action kind");
  }
};

export function decodeFlowDocument(value: Json): FlowDocument {
  requireWellFormed(value, "flow document");
  const owners = new Set<string>();
  const document: FlowDocument = [];
  for (const raw of array(value)) {
    const graph = object(raw);
    exact(graph, ["owner", "bodySpans", "entry", "cells", "prologue", "nodes", "moduleReads"]);
    const ownerSpan = span(graph.owner);
    const prologue =
      graph.prologue === null ? null : bindingPlan(graph.prologue);
    const bodySpans = array(graph.bodySpans).map(span);
    const cells = scope(graph.cells);
    const owner = ownerSpan.join(":");
    if (owners.has(owner)) invalid("duplicate graph owner");
    owners.add(owner);
    const nodes = array(graph.nodes);
    const edge = (target: unknown): number => {
      const index = nat(target);
      if (index >= nodes.length) invalid("edge names a missing node");
      return index;
    };
    const entry = edge(graph.entry);
    const decodedNodes = nodes.map((rawNode, id): FlowNode => {
      const node = object(rawNode);
      exact(node, [
        "id",
        "point",
        "source",
        "scope",
        "handler",
        "action",
        "executions",
        "bindingPlan",
      ]);
      const point = `${owner}:${id}`;
      const nodeId = nat(node.id);
      if (nodeId !== id || node.point !== point) invalid("node identity");
      const source = span(node.source);
      const nodeScope = scope(node.scope);
      const decodedBindingPlan =
        node.bindingPlan === null ? null : bindingPlan(node.bindingPlan);
      const executions = array(node.executions).map(
        (rawExecution): SourceExecution => {
          const execution = object(rawExecution);
          exact(execution, ["source", "plan"]);
          const source = span(execution.source);
          const decodedPlan = planOf(execution.plan);
          return { source, plan: decodedPlan };
        },
      );
      let handler: FlowHandler | null = null;
      if (node.handler !== null) {
        const h = object(node.handler);
        exact(h, ["target", "scope", "binding"]);
        const target = edge(h.target);
        const handlerScope = scope(h.scope);
        const handlerBinding = bindingOf(h.binding);
        handler = { target, scope: handlerScope, binding: handlerBinding };
      }
      const action = flowAction(node.action, edge);
      return {
        id: nodeId,
        point,
        source,
        scope: nodeScope,
        handler,
        action,
        executions,
        bindingPlan: decodedBindingPlan,
      };
    });
    document.push({
      owner: ownerSpan,
      prologue,
      bodySpans,
      moduleReads: array(graph.moduleReads).map(text),
      cells,
      entry,
      nodes: decodedNodes,
    });
  }
  return document;
}
