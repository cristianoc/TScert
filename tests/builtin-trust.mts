// The built-ins' trust fields (SOURCE-CONTRACTS.md, "A built-in's trust
// fields"): each value that makes a built-in outside code has a run under
// Node showing the behaviour, and a contract missing a field is refused.
import assert from "node:assert/strict";
import { checkTrust, outsideCode, withinB, type BuiltinTrust } from "../tools/builtin-trust.mts";
import { globalsOverlay } from "../tools/library-globals.mts";
import { intrinsicTrust } from "../tools/intrinsics.mts";

const tick = (): Promise<void> => new Promise(resolve => setTimeout(resolve, 0));

/** A promise whose own `then` records the functions it is passed. */
function recordingThen(): { p: Promise<number>; passed: unknown[][] } {
  const p = Promise.resolve(1);
  const passed: unknown[][] = [];
  const then = p.then.bind(p);
  Object.assign(p, { then: (...args: Parameters<typeof then>) => { passed.push(args); return then(...args); } });
  return { p, passed };
}

/** Each run shows the behaviour of the values its built-in states. */
const runs: Readonly<Record<string, () => Promise<void>>> = {
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

const outside: [string, BuiltinTrust][] = [
  ...globalsOverlay.map((e): [string, BuiltinTrust] => [`${e.global}${e.member === undefined ? "" : `.${e.member}`}`, e.trust]),
  ...intrinsicTrust.entries()].filter(([, trust]) => outsideCode(trust));
for (const [name] of outside) {
  const run = runs[name];
  assert(run !== undefined, `the built-in ${name} is read as outside code and has no run under Node showing why`);
  await run();
}

// A contract missing a field, or stating a value its effects do not, is
// refused.
assert.throws(() => checkTrust("x", { onThrow: "top", stores: "operands", passesOwnAllocations: false, spec: "s" }, []),
  /the built-in x's contract states no callsArgs/);
assert.throws(() => checkTrust("x", { ...withinB("s", "top"), spec: "" }, []), /cites no section/);
assert.throws(() => checkTrust("x", withinB("s", "footprint"), [undefined]), /states onThrow footprint, its effects top/);
process.stdout.write(`built-in trust: ${outside.length} built-ins read as outside code, each shown under Node\n`);
