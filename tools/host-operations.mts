/** The audit of the fragment's operations against restricted values
 * (HOST-FAMILIES.md, "Operations and their obligations"): each source form
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
  instanceOfErrorName, instanceOfMapName, instanceOfSetName, assertionFailureName, ownKeysName, prototypeIsObjectName,
  ordinaryHasInstanceName, importMetaDirnameName, importMetaFilenameName, importMetaResolveName, importMetaUrlName,
} from "./intrinsics.mts";

/** The key capability for an open read, independent of the receiver's
 * apparent type: erasing a host value to unknown preserves this gate.
 *
 * Audit of these eight keys and of `receiverOpenReadKeys`' two against
 * every admitted family and overlay (an implementation audit of the
 * installed package and Node; C5 of tests/compiler-api.mts samples it):
 * - Compiler nodes: kind is RemoteNodeBase's byte-reading getter (or a
 *   NodeObject data field); getStart is a prototype method; name, and the
 *   receiver-restricted body and type, read the encoded named child (RemoteNode.getNamedChild, undefined
 *   for a kind without that child) or NodeObject._data's field, on every
 *   node, whatever its kind. The child is a family node or undefined; lazy
 *   wrappers/cache writes are host bookkeeping, outside the modeled heap.
 *   The other keys are absent.
 * - Node lists (RemoteNodeList and factory arrays): all ten keys absent,
 *   including along Array.prototype and Object.prototype.
 * - Sync API/client/channel: close is a prototype method; the other keys
 *   are absent. Snapshot, Project, Program, Checker, Type and Signature
 *   have none; Symbol.name is a string data field, NodeHandle.kind a
 *   numeric data field, a type predicate's type a data field holding a
 *   Type or undefined. Other compiler response records carry ordinary
 *   contract values. See dist/api/sync/{api,client}.js, syncChannel.js and
 *   dist/{api/node/node.generated,api/node/node.infrastructure,ast/factory.generated}.js.
 * - Channel ChildProcess: kill and inherited EventEmitter.once are data
 *   methods; exitCode and signalCode are own data (number/string or null).
 *   Node's process has kill/once data methods and an exitCode getter reading
 *   internal exit fields only (number or undefined); the other keys absent.
 * - Library overlays: Timeout.close and Hash's inherited once are data
 *   methods; Dirent/DirentFromStats.name and Error's inherited name are
 *   string data. Stats/BigIntStats, Uint8Array/Buffer, TextDecoder, Date,
 *   Set/Map and their iterators, RegExp and its iterator, Promise and
 *   ordinary arrays have none of these keys. Node's lib/internal/process/
 *   per_thread.js, timers.js, events.js, internal/fs/utils.js and the
 *   standard prototype contracts supply these descriptors.
 *
 * Every listed value meets unknown, including callable values: reading a
 * method does not call it or grant its callable contract. Getter execution
 * preserves the modeled heap. Standard prototypes and host implementations
 * retain these audited descriptors; external ordinary objects obey the
 * open-read restriction of SOURCE-CONTRACTS.md. Any new family, overlay or
 * key requires this cross-family audit again. Absence includes inheritance.
 * A data descriptor alone grants no permission to expose host internals. */
export const auditedOpenReadKeys: ReadonlySet<string> = new Set([
  "close", "kill", "once", "exitCode", "signalCode", "kind", "getStart", "name",
]);

/** Open-read keys admitted only where every arm of the receiver's type
 * states the key or is of the host package, its declarations and its base
 * types' all the package's, whose audit above covers the key. An arm of the
 * program's own type stating no key, which may carry a getter there, of a
 * type extending an external one, of another library's type, `object` or
 * `unknown` keeps the read refused. */
export const receiverOpenReadKeys: ReadonlySet<string> = new Set(["body", "type"]);

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
  coalesce: value, optional: value, withObject: value, lambda: value, blockBody: value, assign: value, nullishAssign: value,
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
  tagMember: transparent("the name, or its tag field, a stated member read once, compared with each tag"),
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
 * `%RestFrom:k%` and `%Read:k%` by their prefixes. */
export const intrinsicForms: Readonly<Record<string, HostClass>> = {
  [awaitName]: transparent("a value at a Promise type: a realm promise by the await assumption"),
  [asyncReturnName]: value, [asyncCompleteName]: value,
  [promiseResolveName]: transparent("a stably non-thenable value or a realm promise"),
  [promiseAllName]: transparent("elements at Promise types: realm promises by the await assumption"),
  [promiseRejectName]: value, [newPromiseName]: calls,
  [assertionFailureName]: transparent("allocates an AssertionError from a string message"),
  [instanceOfErrorName]: transparent("a prototype chain walk for Error.prototype, which no host prototype is"),
  [instanceOfMapName]: transparent("a prototype chain walk for Map.prototype, which no host prototype is"),
  [instanceOfSetName]: transparent("a prototype chain walk for Set.prototype, which no host prototype is"),
  [ordinaryHasInstanceName]: transparent("a prototype chain walk for a class's prototype, which no host prototype is; no proxy on the chain (DESIGN.md's no-proxy row)"),
  [ownKeysName]: obligated("the object", "runs its [[OwnPropertyKeys]], code of a host exotic object"),
  [prototypeIsObjectName]: obligated("the object", "runs its [[GetPrototypeOf]], code of a host exotic object"),
  [symbolForName]: value, [symbolKeyForName]: value,
  [importMetaUrlName]: value, [importMetaDirnameName]: value, [importMetaFilenameName]: value,
  [importMetaResolveName]: value,
  [iterateName]: store,
  [iterateStringName]: value, [iterateSetName]: value, [iterateMapName]: value, [iterateIteratorName]: value,
  [iterateRegExpStringName]: value,
  [forInName]: transparent("strings, which is all its contract states"),
  [iterateForInName]: transparent("over a dictionary, whose family admits no host object"),
  [hasPropertyName]: transparent("HasProperty over own fields and the prototype chain, as at run time (T4)"),
  [elementAtName]: store,
  "%Spread:": transparent("a string, Set, Map or iterator: no host value"),
  "%RestFrom:": store,
  "%Read:": transparent("the value at a key in auditedOpenReadKeys, at unknown: absence, a data property or an audited transparent getter "
    + "for every admitted host family, including through erasure; external objects obey the open-read restriction"),
};

/** The overlay tables of `array-prototype.mts`, each classified whole. */
export const overlayTables: Readonly<Record<"array" | "primitive" | "interface", HostClass>> = {
  array: transparent("a node list inherits each member but `at` and its iterator; `at`'s override and the "
    + "generator meet their contracts; the conversion members hold only under the complete conversion "
    + "contract, which nodes meet nowhere"),
  primitive: transparent("the receiver is a primitive"),
  interface: transparent("the receiver is a realm Set, Map or Date, whose members no host object has"),
};
