// The single pass's controls (`TSCERT_ROUTE=single-pass`, docs/drafts/single-pass.md):
// the inputs no case makes on the single-pass route, each control a block of
// this file run by a pool of control processes, one per core, every
// operation replayed from the stage store as pipeline/test.mts's controls'
// are (STAGE-STORE.md, "Controls"). A case is checked on the route (the
// parse, then `verifier --verify-interface-stage 8` with the interface
// stages it needs); a control then runs the pass over its fragment under a
// forced proposal (`TSCERT_FORCE`), or over a forged fragment, and requires
// the unit it names refused. The store-boundary controls of the interface
// stages name a fresh store.
import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { availableParallelism } from "node:os";
import { fork } from "node:child_process";
import { controlOperations, ran as ranStage, startEviction, type Invoked } from "../pipeline/stages.mts";
import { check as checkSource } from "../pipeline/verify-source.mts";
import { verifyWithInterfaces } from "../pipeline/module-interfaces.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { linkFixtures } from "../pipeline/fixture-links.mts";
import { cases } from "../pipeline/cases.mts";
import type { Ast } from "../tools/fragment.mts";
import { forcedProposals, interfaceControls } from "./single-pass-control-inputs.mts";

process.env.TSCERT_ROUTE = "single-pass";
const root = resolve(import.meta.dirname, "..");
const isObject = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}

/** A finished operation a control ran, counted as an executed or a replayed
 * one (`tested`'s count); a replayed timeout or an unfinished one fails it. */
function counted(invoked: Invoked): Invoked {
  const { execution } = invoked.record;
  if (execution === "replayed") controlOperations.replayed++;
  else if (ranStage(invoked.record)) {
    controlOperations.executed++;
    controlOperations.elapsedMs += invoked.record.elapsedMs;
  } else throw Error(`control: ${invoked.record.stage} neither ran nor replayed a finished result (${execution})`);
  return invoked;
}

/** A unit's verdict from the pass: accepted, and closed when it and every
 * unit it depends on are accepted (a module unit only where its line is
 * printed), as the route reads it. */
type Verdict = { accepted: boolean; closed: boolean; refusal: string };
/** The pass over `fragment` under `force` (none for an unforced run). */
type Pass = { status: number | null; stdout: string; stderr: string; verdicts: Map<string, Verdict> };
function pass(fragment: string, force: readonly string[] = [], names: string = ""): Pass {
  const work = runDirectory("single-pass-control-");
  const given = join(work, "given.jsonl"), standins = join(work, "standins.json");
  writeFileSync(given, "");
  writeFileSync(standins, '{"functions":[],"imports":[]}');
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  const key = isObject(ast) && typeof ast.file === "string" ? ast.file : "";
  const { run, interfaces } = verifyWithInterfaces(fragment, key, names, standins, { mode: 8, fuel: 12, rounds: 4096,
    force, allCuts: false, given, work: join(work, "interfaces"),
    invocation: { limitMs: 60_000, force: false, recorder: null } });
  for (const r of interfaces.records) counted(r);
  counted(run);
  const verdicts = new Map<string, Verdict>();
  const depends = new Map<string, string[]>();
  for (const line of run.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const value: unknown = JSON.parse(line);
    if (!isObject(value) || typeof value.unit !== "string") continue;
    const accepted = value.accepted === true;
    verdicts.set(value.unit, { accepted, closed: accepted, refusal: typeof value.refusal === "string" ? value.refusal : "" });
    depends.set(value.unit, Array.isArray(value.depends) ? value.depends.filter((d) => typeof d === "string") : []);
  }
  for (let changed = true; changed; ) {
    changed = false;
    for (const [unit, v] of verdicts) {
      if (v.closed && (depends.get(unit) ?? []).some((d) => verdicts.get(d)?.closed === false ||
          (d.startsWith("module:") && !verdicts.has(d)))) {
        v.closed = false;
        changed = true;
      }
    }
  }
  return { status: run.status, stdout: run.stdout, stderr: run.stderr, verdicts };
}
/** The pass's words: its refusal (standard error) and its verdicts. */
const words = (p: Pass): string => p.stderr + p.stdout;
/** Require `unit` accepted with every unit it depends on. */
function accepted(p: Pass, unit: string, what: string): void {
  assert.equal(p.verdicts.get(unit)?.closed, true, `${what}: ${unit} not accepted: ${words(p).slice(0, 2000)}`);
}
/** Require `unit` refused: its own refusal, or a unit it depends on
 * refused; or the file refused before any unit's verdict (the front).
 * `at` the refusal's text where the control states it. */
function refused(p: Pass, unit: string, what: string, at?: RegExp): void {
  const v = p.verdicts.get(unit);
  assert.ok(v === undefined ? p.status !== 0 : !v.closed, `${what}: ${unit} accepted: ${words(p).slice(0, 2000)}`);
  if (at !== undefined) assert.match(v === undefined || v.refusal === "" ? words(p) : v.refusal, at, what);
}
/** Require the file refused: a unit refused, or the front. */
function refusedFile(p: Pass, what: string, at?: RegExp): void {
  assert.ok(p.status !== 0 || [...p.verdicts.values()].some((v) => !v.closed), `${what}: accepted: ${words(p).slice(0, 2000)}`);
  if (at !== undefined) assert.match(words(p), at, what);
}

/** A case checked on the single-pass route, its artifacts retained: one
 * run per case in a control process, its own to write beside. */
const caseRuns = new Map<string, string>();
function run(file: string): string {
  const held = caseRuns.get(file);
  if (held !== undefined) return held;
  const test = must(cases.find((c) => c.file === file), `case ${file}`);
  const outcome = checkSource(join(root, "pipeline/examples", `${file}.ts`),
    test.project ? tsconfigOf(resolve(root, test.project)) : undefined, test.typescriptErrors, undefined, true);
  assert.notEqual(outcome.status, "error", `${file}: ${outcome.status === "verified" ? "" : outcome.detail}`);
  caseRuns.set(file, outcome.artifacts);
  return outcome.artifacts;
}
const fragmentOf = (artifacts: string): string => join(artifacts, "fragment.json");
/** Write a forged parser document beside a run's artifacts. */
function forged(artifacts: string, name: string, document: Ast | Record<string, unknown>): string {
  const path = join(artifacts, `${name}.json`);
  writeFileSync(path, JSON.stringify(document) ?? "");
  return path;
}

const controls: { name: string; body: () => Promise<void> }[] = [];
const control = (name: string, body: () => Promise<void>): void => {
  controls.push({ name, body });
};
const serving: boolean = process.argv[2] === "--controls";
const say = (line: string): void => {
  process.stdout.write(`${line}\n`);
};

// ---------------------------------------------------------------------------
// Forced proposals: the type computation states something false; the unit is
// then refused. A positive case's unit is accepted unforced.

for (const k of forcedProposals) {
  control(`forced ${k.force}: ${k.file} ${k.unit}`, async (): Promise<void> => {
    const fragment = fragmentOf(run(k.file));
    const unforced = pass(fragment);
    if (k.positive) accepted(unforced, k.unit, `${k.file} unforced`);
    else refused(unforced, k.unit, `${k.file} unforced`);
    refused(pass(fragment, k.force.split(",")), k.unit, `${k.file} forced ${k.force}`, k.at);
    say(`forced ${k.force}: ${k.file} ${k.unit} ${k.positive ? "accepted unforced, " : ""}refused forced`);
  });
}

// ---------------------------------------------------------------------------
// Module interfaces: the store boundary of the interface stages.

control("module interfaces: the store boundary", async (): Promise<void> => {
  const artifacts = run("certified-value-import");
  const given = join(artifacts, "control-given.jsonl");
  writeFileSync(given, "");
  interfaceControls(fragmentOf(artifacts), given, join(artifacts, "interface-controls"), say, counted);
});

// ---------------------------------------------------------------------------
// The pool.

type Operations = { executed: number; replayed: number; elapsedMs: number };
type Finished = { finished: number; error: string | null; operations: Operations; retiring: boolean };
const readFinished = (value: unknown): Finished => {
  if (!isObject(value) || typeof value.finished !== "number" || !(value.error === null || typeof value.error === "string") ||
      typeof value.retiring !== "boolean" || !isObject(value.operations))
    throw Error(`not a control's result: ${JSON.stringify(value)}`);
  const o = value.operations;
  if (typeof o.executed !== "number" || typeof o.replayed !== "number" || typeof o.elapsedMs !== "number")
    throw Error(`not a control's result: ${JSON.stringify(value)}`);
  return { finished: value.finished, error: value.error, retiring: value.retiring,
    operations: { executed: o.executed, replayed: o.replayed, elapsedMs: o.elapsedMs } };
};
const chosen = process.argv.slice(serving ? 3 : 2);
if (serving) {
  // A control process: one control per message. A process whose caches may
  // disagree with the file system reports its control and exits.
  process.on("message", (message: unknown) => {
    if (!isObject(message) || typeof message.control !== "number") throw Error(`not a control's request: ${JSON.stringify(message)}`);
    const index = message.control;
    const entry = controls[index];
    if (entry === undefined) throw Error(`no control ${index}`);
    const before = { ...controlOperations };
    const report = (error: string | null): void => {
      const retiring = processInconsistency() !== null || processRetirement() !== null;
      const finished: Finished = { finished: index, error, retiring, operations: {
        executed: controlOperations.executed - before.executed, replayed: controlOperations.replayed - before.replayed,
        elapsedMs: controlOperations.elapsedMs - before.elapsedMs } };
      process.send?.(finished, () => {
        if (retiring) process.exit(0);
      });
    };
    entry.body().then(() => report(null), (error: unknown) =>
      report(error instanceof Error ? error.stack ?? error.message : String(error)));
  });
  process.on("disconnect", () => process.exit(0));
} else {
  // `node tests/single-pass-controls.mts [pattern…]`: the controls whose
  // names contain a pattern, every one with none.
  startEviction();
  linkFixtures();
  const started = performance.now();
  const failures: string[] = [];
  const tally: Operations = { executed: 0, replayed: 0, elapsedMs: 0 };
  const pending = controls.flatMap((c, i) => chosen.length === 0 || chosen.some((p) => c.name.includes(p)) ? [i] : []);
  const total = pending.length;
  let processes = 0;
  const width = Math.max(1, Math.min(availableParallelism(), pending.length));
  const lane = (): Promise<void> => new Promise<void>((done, fail) => {
    processes++;
    const child = fork(import.meta.filename, ["--controls"], { stdio: ["ignore", "pipe", "pipe", "ipc"] });
    let printed = "", errors = "", retired = false;
    child.stdout?.setEncoding("utf8");
    child.stdout?.on("data", (text: unknown) => {
      printed += String(text);
      const at = printed.lastIndexOf("\n");
      if (at >= 0) {
        process.stdout.write(printed.slice(0, at + 1));
        printed = printed.slice(at + 1);
      }
    });
    child.stderr?.setEncoding("utf8");
    child.stderr?.on("data", (text: unknown) => { errors += String(text); });
    const give = (): void => {
      const index = pending.shift();
      if (index !== undefined) child.send({ control: index });
      else child.disconnect();
    };
    child.on("message", (message: unknown) => {
      const result = readFinished(message);
      tally.executed += result.operations.executed;
      tally.replayed += result.operations.replayed;
      tally.elapsedMs += result.operations.elapsedMs;
      if (result.error !== null) failures.push(`${controls[result.finished]?.name ?? result.finished}: ${result.error}`);
      if (result.retiring) retired = true;
      else give();
    });
    child.on("error", fail);
    child.on("exit", (status: number | null) => {
      if (printed) process.stdout.write(printed + "\n");
      if (status !== 0) failures.push(`a control process exited with ${status}: ${errors}`);
      if (retired && status === 0 && pending.length > 0) lane().then(done, fail);
      else done();
    });
    give();
  });
  await Promise.all(Array.from({ length: width }, lane));
  process.stdout.write(`single-pass controls: ${total} in ${((performance.now() - started) / 1000).toFixed(1)} s on ${width} ` +
    `lanes (${processes} processes); their operations ${tally.executed} executed (${(tally.elapsedMs / 1000).toFixed(1)} s ` +
    `in all), ${tally.replayed} replayed\n`);
  assert.deepEqual(failures, [], failures.join("\n"));
}
