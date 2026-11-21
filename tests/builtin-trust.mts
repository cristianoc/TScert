// The built-ins' trust fields (SOURCE-CONTRACTS.md, "A built-in's trust
// fields"): each value that makes a built-in outside code has a run under
// Node showing the behaviour, and a contract missing a field is refused.
import assert from "node:assert/strict";
import { stripTypeScriptTypes } from "node:module";
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import { checkStatedTrust, checkTrust, outsideCode, withinB, type BuiltinTrust } from "../tools/builtin-trust.mts";
import { globalsOverlay } from "../tools/library-globals.mts";
import { intrinsicTrust, iterationIntrinsic } from "../tools/intrinsics.mts";
import { typeMemberTrust } from "../tools/library-types.mts";
import { hashMemberTrust, modulesOverlay } from "../tools/library-modules.mts";
import { compilerApiFamily } from "../tools/compiler-api.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { emptyEffect } from "../tools/type-graph.mts";

const tick = (): Promise<void> => new Promise(resolve => setTimeout(resolve, 0));

/** A promise whose own `then` records the functions it is passed. */
function recordingThen(): { p: Promise<number>; passed: unknown[][] } {
  const p = Promise.resolve(1);
  const passed: unknown[][] = [];
  const then = p.then.bind(p);
  Object.assign(p, { then: (...args: Parameters<typeof then>) => { passed.push(args); return then(...args); } });
  return { p, passed };
}

/** A TypeScript source file of the compiler's API, and the number of nodes
 * its node table holds: the storage the file's methods materialize nodes
 * into. */
function sourceFile(text: string): { file: ReturnType<typeof openText>; held: () => number } {
  const path = join(runDirectory("tscert-trust-"), "probe.ts");
  writeFileSync(path, text);
  const file = openText(path, text);
  const held = (): number => {
    const nodes: unknown = Reflect.get(file, "nodes");
    return Array.isArray(nodes) ? nodes.filter(n => n !== undefined).length : -1;
  };
  return { file, held };
}

/** Each run shows the behaviour of the values its built-in states. */
const runs: Readonly<Record<string, () => Promise<void>>> = {
  // A validation function is called with `this` a fresh object.
  "assert/strict.throws": async () => {
    const receivers: unknown[] = [];
    assert.throws(() => { throw Error("x"); }, function (this: unknown) { receivers.push(this); return true; });
    const [r] = receivers;
    assert(typeof r === "object" && r !== null && Object.keys(r).length === 0);
  },
  "assert/strict.doesNotThrow": async () => {
    const receivers: unknown[] = [];
    try { assert.doesNotThrow(() => { throw Error("x"); }, function (this: unknown) { receivers.push(this); return true; }); }
    catch { /* the block threw */ }
    const [r] = receivers;
    assert(typeof r === "object" && r !== null && Object.keys(r).length === 0);
  },
  // The first call queues an `ExperimentalWarning`, which it allocates, on
  // the realm's tick queue: a `warning` listener receives it after the call
  // returns.
  "module.stripTypeScriptTypes": async () => {
    const warnings: unknown[] = [];
    const listener = (w: unknown): void => { warnings.push(w); };
    process.on("warning", listener);
    stripTypeScriptTypes("const a: number = 1;");
    assert(warnings.length === 0);
    await tick();
    process.off("warning", listener);
    assert(warnings.some(w => w instanceof Error && w.name === "ExperimentalWarning"));
  },
  // `forEachChild` creates each child it visits, stores it into the file's
  // node table and passes it to the visitor.
  "Node.forEachChild": async () => {
    const { file, held } = sourceFile("const a = 1;\n");
    const [statement] = file.statements;
    assert(statement !== undefined);
    const before = held();
    const visited: unknown[] = [];
    statement.forEachChild(child => { visited.push(child); return undefined; });
    assert(visited.length > 0 && held() > before);
  },
  // `getStart` with JSDoc creates the node's JSDoc nodes into the table.
  "Node.getStart": async () => {
    const { file, held } = sourceFile("/** d */\nconst a = 1;\n");
    const [statement] = file.statements;
    assert(statement !== undefined);
    const before = held();
    statement.getStart(file, true);
    assert(held() > before);
  },
  // The first position mapped stores the file's line starts, a fresh array,
  // into the file.
  "SourceFile.getLineAndCharacterOfPosition": async () => {
    const { file } = sourceFile("a;\nb;\n");
    assert(Reflect.get(file, "_lineStarts") === undefined);
    file.getLineAndCharacterOfPosition(3);
    assert(Array.isArray(Reflect.get(file, "_lineStarts")));
  },
  // A reviver is called with `this` the holder object `{ "": result }`,
  // which the run allocates.
  "JSON.parse": async () => {
    const holders: unknown[] = [];
    const parse: (text: string, reviver: (this: unknown, key: string, value: unknown) => unknown) => unknown = JSON.parse;
    parse("[1]", function (this: unknown, key: string, value: unknown) { if (key === "") holders.push(this); return value; });
    const [holder] = holders;
    assert(typeof holder === "object" && holder !== null && Object.keys(holder).length === 1 && "" in holder);
  },
  // A replacer is called with `this` the wrapper `{ "": value }`, which the
  // run allocates and stores its argument into.
  "JSON.stringify": async () => {
    const value = { a: 1 };
    const holders: unknown[] = [];
    JSON.stringify(value, function (this: unknown, key: string, v: unknown) { if (key === "") holders.push(this); return v; });
    const [holder] = holders;
    assert(typeof holder === "object" && holder !== null && holder !== value && "" in holder && holder[""] === value);
  },
  // A listener is kept and called after the call returns.
  "process.on": async () => {
    let called = false;
    const listener = (): void => { called = true; };
    process.on("beforeExit", listener);
    assert(!called);
    process.emit("beforeExit", 0);
    process.off("beforeExit", listener);
    assert(called);
  },
  "process.once": async () => {
    let called = false;
    process.once("beforeExit", () => { called = true; });
    assert(!called);
    process.emit("beforeExit", 0);
    assert(called);
  },
  // The callback is kept and called after the call returns.
  "setTimeout": async () => {
    let called = false;
    setTimeout(() => { called = true; }, 0);
    assert(!called);
    await tick();
    assert(called);
  },
  // Each element's `then` is passed functions the run allocates, stored
  // among the element's reactions.
  "Promise.all": async () => {
    const { p, passed } = recordingThen();
    void Promise.all([p]);
    const [args] = passed;
    assert(args !== undefined && args.length === 2 && args.every(f => typeof f === "function"));
  },
  "%PromiseAll%": async () => runs["Promise.all"]?.(),
  // The executor is passed the resolving functions the run allocates.
  "Promise": async () => {
    const passed: unknown[] = [];
    void new Promise((resolve, reject) => { passed.push(resolve, reject); });
    assert(passed.length === 2 && passed.every(f => typeof f === "function"));
  },
  "%NewPromise%": async () => runs["Promise"]?.(),
  // `await p` stores the function's continuation among p's reactions:
  // resolving p, storage that existed before the await, runs it.
  "%Await%": async () => {
    let resolve: (v: number) => void = () => {};
    const p = new Promise<number>(r => { resolve = r; });
    let after = false;
    void (async () => { await p; after = true; })();
    await tick();
    assert(!after);
    resolve(1);
    await tick();
    assert(after);
  },
  // Returning a promise from an async function passes the function's
  // resolving functions, which the run allocates, to its `then`.
  "%AsyncReturn%": async () => {
    const { p, passed } = recordingThen();
    void (async () => p)();
    await tick();
    const [args] = passed;
    assert(args !== undefined && args.length === 2 && args.every(f => typeof f === "function"));
  },
};

// `Error.captureStackTrace(o)`, which no contract states (outside code by
// its declaration's origin, `@types/node`): it installs the realm's accessor
// functions on `o`, storage that existed before its call.
{
  const o = {};
  Error.captureStackTrace(o);
  const d = Object.getOwnPropertyDescriptor(o, "stack");
  assert(d !== undefined && typeof d.get === "function" && typeof d.set === "function");
}

/** The built-ins read as outside code that Node does not provide, each
 * with the section showing the value: a browser's DOM. */
const notInNode: Readonly<Record<string, string>> = {
  // The first `getContext("2d")` stores the context it creates into the
  // canvas's context slot.
  "OffscreenCanvas.getContext": "HTML, OffscreenCanvas getContext: set this's context to the new context",
  // A tree or attribute change queues a mutation record it allocates on
  // each registered observer's record queue.
  "Element.appendChild": "DOM, insert: queue a tree mutation record",
  "Element.removeChild": "DOM, remove: queue a tree mutation record",
  "InlineStyle.setProperty": "CSSOM, update style attribute: DOM, queue an attribute mutation record",
};

const named = <T,>(entries: readonly T[], name: (e: T) => string, trust: (e: T) => BuiltinTrust): [string, BuiltinTrust][] =>
  entries.map((e): [string, BuiltinTrust] => [name(e), trust(e)]);
const outside: [string, BuiltinTrust][] = [
  ...named(globalsOverlay, e => `${e.global}${e.member === undefined ? "" : `.${e.member}`}`, e => e.trust),
  ...intrinsicTrust.entries(), ...typeMemberTrust.entries(), ...hashMemberTrust.entries(),
  ...named(modulesOverlay, e => `${e.module}.${e.member ?? e.name}`, e => e.trust),
  ...named(compilerApiFamily.footprints, e => `${e.owner}.${e.member}`, e => e.trust),
].filter(([, trust]) => outsideCode(trust));
// The first call of `stripTypeScriptTypes` in the process is the one that
// warns: its run goes first.
const order = (name: string): number => name === "module.stripTypeScriptTypes" ? 0 : 1;
const shown = new Set<string>();
for (const [name] of [...outside].sort(([a], [b]) => order(a) - order(b))) {
  if (shown.has(name)) continue;
  shown.add(name);
  const run = runs[name];
  if (run === undefined && notInNode[name] !== undefined) continue;
  assert(run !== undefined, `the built-in ${name} is read as outside code and has no run under Node showing why`);
  await run();
}
closeParser();

// Each iteration kind's step and spread, and a union's, state their trust
// fields when made.
for (const kind of ["%Iterate:string%", "%Spread:string%", "%Iterate%|%Iterate:string%"])
  iterationIntrinsic(kind, () => ({ k: "atom", name: "unknown", span: [0, 0] }),
    () => ({ k: "atom", name: "unknown", span: [0, 0] }), () => ({ k: "atom", name: "unknown", span: [0, 0] }));
// A stated type's method without trust fields, or fields naming no method,
// is refused.
assert.throws(() => checkStatedTrust([{ declaration: { module: "m", name: "T", span: [0, 0] }, parameters: [], bases: [],
  expression: { k: "object", stringIndex: null, calls: [], span: [0, 0], fields: [{ name: "f", optional: false, readonly: true,
    span: [0, 0], type: { k: "function", effect: emptyEffect, receiver: null, params: [], rest: null, result: { k: "atom", name: "unknown", span: [0, 0] }, span: [0, 0] } }] } }],
  new Map()), /the built-in T\.f's contract states no trust fields/);
assert.throws(() => checkStatedTrust([], new Map([["T.g", withinB("s", "top")]])), /T\.g name no method/);

// A contract missing a field, or stating a value its effects do not, is
// refused.
assert.throws(() => checkTrust("x", { onThrow: "top", stores: "operands", passesOwnAllocations: false, spec: "s" }, []),
  /the built-in x's contract states no callsArgs/);
assert.throws(() => checkTrust("x", { ...withinB("s", "top"), spec: "" }, []), /cites no section/);
assert.throws(() => checkTrust("x", withinB("s", "footprint"), [undefined]), /states onThrow footprint, its effects top/);
process.stdout.write(`built-in trust: ${shown.size} built-ins read as outside code, ${shown.size - Object.keys(notInNode).length} shown under Node, ${Object.keys(notInNode).length} a browser's\n`);
