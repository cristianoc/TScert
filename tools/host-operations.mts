/** The audit of the fragment's operations against restricted values
 * (COMPILER-API.md, "Operations and their obligations"): each source form
 * the parser admits, each intrinsic it writes and each table of the reviewed
 * library overlays, classified by what its model states of a host object or
 * a node list. The tables are keyed by the parser's own unions, so a form
 * added to the fragment is a type error here until it is classified.
 *
 * - transparent: the model holds of a restricted value as of any value of
 *   the operand's type (a callback keeps its own callable contract);
 * - obligated: a step stuck on a host object, or a library parameter stated
 *   at the non-host values, whose rule requires `excludesHost` of the
 *   listed operands' claimed types;
 * - refused: the fragment does not admit the form.
 *
 * The classification is the reviewed record; Lean enforces the obligated
 * ones by their steps and rules, whatever the producer claims. */
import type { Expr, PatternAst, Stmt } from "./fragment.mts";
import {
  asyncCompleteName, asyncReturnName, awaitName, elementAtName, forInName, hasPropertyName, iterateForInName,
  iterateIteratorName, iterateMapName, iterateName, iterateRegExpStringName, iterateSetName, iterateStringName,
  newPromiseName, promiseAllName, promiseRejectName, promiseResolveName, symbolForName, symbolKeyForName,
} from "./intrinsics.mts";

export type HostClass =
  | { k: "transparent"; why: string }
  | { k: "obligated"; operands: string; why: string }
  | { k: "refused"; why: string };

export const transparent = (why: string): HostClass => ({ k: "transparent", why });
export const obligated = (operands: string, why: string): HostClass => ({ k: "obligated", operands, why });

const value = transparent("binds, passes or tests a value; observes no member");
const read = transparent("a stated member's value, a view of the record the model reads");
const store = transparent("a node list's store: its table, by T4");
const writes = transparent("writes an invariant field or a writable store, whose families admit no host object");
const calls = transparent("a call: the callee's contract; a callback keeps its own");

export const expressionForms: { readonly [K in Expr["k"]]: HostClass } = {
  id: value, this: value, lit: value, not: value, cast: value, comma: value, conditional: value,
  coalesce: value, optional: value, lambda: value, blockBody: value, assign: value, nullishAssign: value,
  alloc: transparent("allocates an ordinary object"),
  ctor: transparent("allocates an ordinary class value"),
  build: obligated("each spread operand", "a fresh record of the operand's members as own keys"),
  read, index: read,
  arrayLit: store,
  arrayAssign: store,
  indexWrite: writes, write: writes, update: writes, logicalAssign: writes,
  bin: value, arith: value, unary: value,
  withValue: transparent("allocates an ordinary callable object"),
  objectAssign: obligated("the target and each source", "copies each source's own keys onto the target"),
  typeofTest: transparent("the type tag: \"object\" for every host value"),
  arrayTest: transparent("the store: true exactly of node lists among host values"),
  inTest: transparent("HasProperty over own fields and the prototype chain, as at run time (T4)"),
  instanceTest: transparent("a client class's key, which no host prototype owns"),
  apply: calls, new: calls, invoke: calls,
  applyWithReceiver: transparent("the list's length and indices: a node list's table"),
  callWithReceiver: calls, bindWithReceiver: calls,
};

export const statementForms: { readonly [K in Stmt["k"]]: HostClass } = {
  effect: value, return: value, break: value, continue: value, while: value, block: value, if: value,
  throw: value, try: value, const: value, let: value, closing: value,
  forOf: transparent("the iteration intrinsic of the iterable's type, classified below"),
  destructure: transparent("the pattern's forms, classified below"),
};

export const patternForms: { readonly [K in PatternAst["k"]]: HostClass } = {
  name: value,
  array: store,
  object: obligated("the source, where the pattern has a rest", "a rest is a fresh record of the source's other members"),
};

/** The intrinsics the parser writes, by name; `%Spread:K%` and
 * `%RestFrom:k%` by their prefixes. */
export const intrinsicForms: Readonly<Record<string, HostClass>> = {
  [awaitName]: transparent("a value at a Promise type: a realm promise by the await assumption"),
  [asyncReturnName]: value, [asyncCompleteName]: value,
  [promiseResolveName]: transparent("a stably non-thenable value or a realm promise"),
  [promiseAllName]: transparent("elements at Promise types: realm promises by the await assumption"),
  [promiseRejectName]: value, [newPromiseName]: calls,
  [symbolForName]: value, [symbolKeyForName]: value,
  [iterateName]: store,
  [iterateStringName]: value, [iterateSetName]: value, [iterateMapName]: value, [iterateIteratorName]: value,
  [iterateRegExpStringName]: value,
  [forInName]: transparent("strings, which is all its contract states"),
  [iterateForInName]: transparent("over a dictionary, whose family admits no host object"),
  [hasPropertyName]: transparent("HasProperty over own fields and the prototype chain, as at run time (T4)"),
  [elementAtName]: store,
  "%Spread:": transparent("a string, Set, Map or iterator: no host value"),
  "%RestFrom:": store,
};

/** The overlay tables of `array-prototype.mts`, each classified whole. */
export const overlayTables: Readonly<Record<"array" | "primitive" | "interface", HostClass>> = {
  array: transparent("a node list inherits each member but `at` and its iterator; `at`'s override and the "
    + "generator meet their contracts; the conversion members hold only under the complete conversion "
    + "contract, which nodes meet nowhere"),
  primitive: transparent("the receiver is a primitive"),
  interface: transparent("the receiver is a realm Set, Map or Date, whose members no host object has"),
};
