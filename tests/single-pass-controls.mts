// The controls: the inputs no pipeline case makes, each control a block of
// this file run by a pool of control processes, one per core, every
// operation replayed from the stage store (STAGE-STORE.md, "Controls"). A
// case is checked through the pipeline (the parse, then `verifier
// --verify-interface-stage 8` with the interface stages it needs); a
// control then runs the pass over its fragment under a forced proposal
// (`--force-proposals`), or over a forged fragment, and requires the unit it
// names refused. Other controls read what the parser's document states or
// run a native counterexample under Node. The controls of the test
// infrastructure (the store-boundary controls of the interface stages, the
// store's cold and warm runs, replay, run retention) run with --infra
// (`make test-infra`), each in a fresh store of its own, beside the observed
// stages' and the declaration sessions' controls.
import assert from "node:assert/strict";
import { chmodSync, cpSync, existsSync, mkdirSync, readdirSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { pathToFileURL } from "node:url";
import { join, resolve } from "node:path";
import { availableParallelism } from "node:os";
import { fork, spawn } from "node:child_process";
import { controlOperations, invokeProcess, invokeWorker, ran as ranStage, readInvocationLog, startEviction, type AttemptRecord, type Invoked }
  from "../pipeline/stages.mts";
import { Store } from "../pipeline/stage-store.mts";
import { runExample } from "../pipeline/run-example.mts";
import { decodeVerdictLine, decodeWorkerPrepared, verifierBuild, verifierCall }
  from "../pipeline/stage-execution.mts";
import { usePassMutationVerifier } from "./single-pass-mutations.mts";
import { check as checkSource, invocationLog, readFragmentFile, readOutcome, sourceKey, type Outcome } from "../pipeline/verify-source.mts";
import { stringFamily } from "../pipeline/string-family.mts";
import type { FamilyDescription } from "../tools/host-families.mts";
import { createHash } from "node:crypto";
import { fileWorkerProtocol, proposalArgs, verifyWithInterfaces } from "../pipeline/module-interfaces.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { linkFixtures } from "../pipeline/fixture-links.mts";
import { compilerApiFamily, hostEnums } from "../tools/compiler-api.mts";
import { useFamiliesForTests } from "../tools/family-activation.mts";
import { deferredIdentity } from "../tools/type-term.mts";
import { cases } from "../pipeline/cases.mts";
import type { Ast, Expr, FunctionAst } from "../tools/fragment.mts";
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import type { StatedFrame, SpineRegion } from "../tools/type-graph.mts";
import { emptyEffect, ordinaryEffect, statedExits } from "../tools/type-graph.mts";
import { entryRowControl, forcedProposals, interfaceControls } from "./single-pass-control-inputs.mts";

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
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  const key = isObject(ast) && typeof ast.file === "string" ? ast.file : "";
  const { run, interfaces } = verifyWithInterfaces(fragment, key, names, { mode: 8, fuel: 12, rounds: 4096,
    force, work: join(work, "interfaces"),
    invocation: { limitMs: 60_000, force: false, recorder: null } });
  for (const r of interfaces.records) counted(r);
  counted(run);
  return passOf(run);
}
/** A pass's run read: its verdicts, each unit's closure computed. */
function passOf(run: Invoked): Pass {
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
/** Words of a pass: its refusal (standard error) and its verdicts. */
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
  const text = v === undefined || v.refusal === "" ? words(p) : v.refusal;
  if (at !== undefined) assert.match(text, at, `${what}: refused otherwise: ${text.slice(0, 1500)}`);
}
/** Require the file refused: a unit refused, or the front. */
function refusedFile(p: Pass, what: string, at?: RegExp): void {
  assert.ok(p.status !== 0 || [...p.verdicts.values()].some((v) => !v.closed), `${what}: accepted: ${words(p).slice(0, 2000)}`);
  if (at !== undefined) assert.match(words(p), at, `${what}: refused otherwise: ${words(p).slice(0, 1500)}`);
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
/** Controls of a forged input the route accepts, each an open decision:
 * kept as written, run only with TSCERT_SINGLE_PASS_STOPS=1 and listed by
 * every run. */
const stops = new Set<number>();
const stop = (name: string, body: () => Promise<void>): void => {
  stops.add(controls.push({ name: `stop: ${name}`, body }) - 1);
};
/** Controls of the test infrastructure, the store, replay and the driver's
 * run directories: run only by `--infra` (`make test-infra`), with the
 * observed stages' and the declaration sessions' controls beside them. */
const infraControls = new Set<number>();
const infraControl = (name: string, body: () => Promise<void>): void => {
  infraControls.add(controls.push({ name, body }) - 1);
};
/** Controls running the pass's mutation verifier (tests/single-pass-mutations.mts):
 * given once the suite's process has built it. */
const mutationControls = new Set<number>();
const mutationControl = (name: string, body: () => Promise<void>): void => {
  mutationControls.add(controls.push({ name: `mutation: ${name}`, body }) - 1);
};
let mutated: string | null = null;
/** The pass of the mutation verifier over an import-free `fragment` (its
 * importer stage at an empty interfaces document), the mutation `name` selected. */
function mutatedPass(fragment: string, name: string, force: readonly string[] = []): Pass {
  const program = must(mutated, "the mutation verifier");
  const work = runDirectory("single-pass-mutation-");
  const interfaces = join(work, "interfaces.json");
  writeFileSync(interfaces, '{"modules":[]}');
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  assert.ok(isObject(ast) && typeof ast.file === "string" && Array.isArray(ast.modules) && ast.modules.length === 0,
    "an import-free fragment");
  const environment: Record<string, string> = { TSCERT_TEST_MUTATIONS: name };
  return passOf(counted(invokeProcess(verifierCall(program, ["--subtype-rounds", "4096", ...proposalArgs(force), "--verify-interface-stage", "8",
    fragment, interfaces, ast.file, "12", ""], environment), { limitMs: 60_000, force: false, recorder: null })));
}
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
// The file worker: a unit's line is a function of the file's check and the
// unit (STAGE-STORE.md, "Worker stages").

control("worker order: proposals and verdicts in fresh, reversed and resumed workers", async (): Promise<void> => {
  const work = runDirectory("single-pass-worker-");
  const key = join(work, "worker.ts");
  const interfaces = join(work, "interfaces.json");
  writeFileSync(interfaces, '{"modules":[]}');

  // factory returns () => 1, use calls factory, and initialization calls
  // factory too. Its inferred result footprint triggers the second round.
  const number: TypeTerm = { k: "atom", name: "number", span: [1, 2] };
  const callable: TypeTerm = { k: "function", effect: ordinaryEffect, receiver: null, params: [],
    rest: null, result: number, span: [2, 3] };
  const callAt = (name: string, n: number): Expr => ({ k: "apply", pos: [n, n + 3], args: [],
    callee: { k: "id", name, pos: [n, n + 1] } });
  const fn = (name: string, n: number, retType: TypeTerm, e: Expr): FunctionAst => ({
    name, namePos: [n, n + 1], retType, typeParams: [], params: [], guard: null, stated: null,
    requires: [], ensures: [], completion: "sync", strict: true, body: [{ k: "return", pos: [n + 2, n + 10], e }],
  });
  const ast: Ast = { file: key, sourceSha256: "0".repeat(64), modules: [], omittedMentions: [],
    declarations: { roots: [], definitions: [], values: [], symbols: [], applications: [] },
    functions: [fn("factory", 10, callable, { k: "lambda", pos: [13, 19], params: [], typeParams: [],
      receiver: null, guard: null, stated: null, requires: [], result: number, completion: "sync",
      body: { k: "lit", pos: [17, 18], lit: { a: "numberlit", v: "1" } } }),
      fn("use", 30, callable, callAt("factory", 34)),
      fn("outer", 80, callable, callAt("use", 84)),
      fn("leaf", 60, number, { k: "lit", pos: [64, 65], lit: { a: "numberlit", v: "0" } })],
    init: [{ k: "effect", pos: [50, 55], e: callAt("factory", 51) }] };

  for (const variant of ["ordinary", "forced", "failed plan"]) {
    const fragment = join(work, variant + ".json");
    // Empty interfaces defer import-scope decoding to group planning.
    writeFileSync(fragment, JSON.stringify(variant === "failed plan" ? { ...ast, modules: [{}] } : ast));
    const args = ["--subtype-rounds", "4096", ...proposalArgs(variant === "forced" ? ["results"] : []),
      "--file-worker", "8", fragment, interfaces, key, "12", ""];
    const worker = (units: readonly string[] | null, selection: string = "") => {
      const p = spawnSync(verifierBuild, [...args.slice(0, -1), selection], { input: JSON.stringify({ units }) + "\n", encoding: "utf8",
        cwd: work, env: { ...process.env, TSCERT_TRACE_PROPOSALS: "1" } });
      assert.equal(p.status, 0, `the file worker: ${p.stderr}`);
      const [prepared, ...lines] = p.stdout.trimEnd().split("\n");
      const answers = p.stderr.trimEnd().split("\n").filter(l => l.startsWith('{"answers":'));
      assert.equal(answers.length, lines.length, "every verdict has its proposal answers");
      return { prepared, lines, answers };
    };
    const all = worker(null);
    const units = decodeWorkerPrepared(all.prepared).selected.map(u => u.unit);
    assert.equal(units.length, 5);
    assert.deepEqual(all.lines.map(l => decodeVerdictLine(l).unit), units);
    const compare = (order: string[]): void => {
      const result = worker(order);
      assert.equal(result.prepared, all.prepared);
      assert.deepEqual(result.lines, order.map(u => all.lines[units.indexOf(u)]));
      assert.deepEqual(result.answers, order.map(u => all.answers[units.indexOf(u)]));
    };
    compare([...units].reverse());
    for (const unit of units) compare([unit]);
    compare([...units].reverse().concat(units));
    const half = units.slice(0, 1);
    compare(units.slice(half.length));

    const factory = must(all.answers[units.indexOf("factory@10")], "factory proposal");
    if (variant === "failed plan") {
      for (const line of all.lines) {
        const verdict = decodeVerdictLine(line);
        assert.ok("refusal" in verdict && verdict.refusal === verdict.elaboration);
        assert.match(verdict.refusal, /unexpected fields: expected \[location, sourceSha256/);
      }
      assert.match(factory, /\["factory",null\]/);
    } else {
      assert.match(factory, /"resultFootprint":\{"array":"keep","value":"keep","view":"keep"\}/,
        "factory offers the returned closure’s footprint");
      assert.ok(all.lines.every(l => "accepted" in decodeVerdictLine(l)));
      const use = decodeVerdictLine(must(all.lines[units.indexOf("use@30")], "use verdict"));
      assert.ok("depends" in use && use.depends.includes("factory@10"));
      if (variant === "ordinary") {
        const alone = worker(null, "factory");
        assert.deepEqual(decodeWorkerPrepared(alone.prepared).selected.map(u => u.unit), ["factory@10"]);
        assert.match(must(alone.answers[0], "factory without a caller"), /\["factory",null\]/);
        assert.match(must(all.answers[units.indexOf("leaf@60")], "leaf proposal"), /\["leaf",null\]/);
      } else
        assert.match(must(all.answers[units.indexOf("leaf@60")], "forced leaf"), /keep/);
    }

    {
      const shadow = spawnSync(verifierBuild, args, { input: '{"units":null}\n', encoding: "utf8",
        cwd: work, env: { ...process.env, TSCERT_GROUP_SHADOW: "replay" } });
      assert.equal(shadow.status, 0, shadow.stderr);
      const checked = new Map<string, string>();
      for (const line of shadow.stderr.split("\n").filter(line => line.startsWith("group-slice "))) {
        const row: unknown = JSON.parse(line.slice("group-slice ".length));
        assert.ok(isObject(row) && typeof row.unit === "string" && typeof row.verdict === "string");
        assert.equal(row.fileVerdict, row.verdict, row.unit);
        assert.equal(row.graphs, variant === "failed plan" ? "both plans unavailable" : "equal", row.unit);
        assert.equal(row.bindings, variant === "failed plan" ? null : true, row.unit);
        assert.equal(row.proposalsEqual, true, row.unit);
        assert.equal(row.relative, variant !== "failed plan", row.unit);
        assert.ok(!checked.has(row.unit));
        checked.set(row.unit, row.verdict);
      }
      assert.deepEqual(units.map(unit => checked.get(unit)), all.lines);
      if (variant === "ordinary") assert.match(must(all.answers[units.indexOf("outer@80")], "outer’s returned closure"), /"resultFootprint":\{"array":"keep","value":"keep","view":"keep"\}/);
    }

    if (variant === "ordinary") {
      const moveSites = (source: Ast): string => must(JSON.stringify(source, (k, v: unknown) => {
        if (["pos", "span", "namePos"].includes(k) && Array.isArray(v))
          return v.map((n: unknown) => typeof n === "number" ? n + 100 : n);
        return v;
      }), "moved Fragment");
      const beforeStore = process.env.TSCERT_STAGE_STORE;
      const beforeProfile = process.env.TSCERT_PROFILE;
      const store = new Store(join(work, "slice-store"));
      try {
        process.env.TSCERT_STAGE_STORE = store.root;
        const check = () => invokeWorker(verifierCall(verifierBuild, args, { TSCERT_SLICE_DRIVER: "1" }),
          fileWorkerProtocol, { limitMs: 60_000, force: false, recorder: null });
        const cold = check();
        assert.deepEqual(cold.parts.map(p => p.stdout.trimEnd()), all.lines);
        assert.equal(cold.slices.executed, units.length);
        assert.equal(check().starts, 0, "the exact file hits before starting a worker");
        writeFileSync(fragment, moveSites(ast));
        const warm = check();
        assert.equal(warm.slices.executed, 0);
        assert.equal(warm.slices.replayed, units.length);
        assert.deepEqual(warm.parts.map(p => p.stdout.trimEnd()), worker(null).lines, "current member and dependency sites");

        const entries = readdirSync(join(store.root, "entries", "pass")).flatMap(k => {
          const r = store.finished("pass", k, null)?.result;
          return r && r.input.includes('"operation":"check-slice"') ? [{ key: k, result: r }] : [];
        });
        assert.equal(entries.length, units.length);
        const entry = must(entries[0], "stored slice");
        const payload: unknown = JSON.parse(entry.result.stdout.toString("utf8"));
        assert.ok(isObject(payload));
        for (const [name, change] of Object.entries({
          operation: { operation: "propose-slice" }, member: { members: ["other@1"] },
          occurrence: { sites: { offsets: [[1, 10]], ranks: [[10, 1]] } },
        })) {
          const forged = new Store(join(work, name));
          process.env.TSCERT_STAGE_STORE = forged.root;
          forged.publishFinished("pass", entry.key, { ...entry.result, stdout: Buffer.from(JSON.stringify({ ...payload, ...change })) });
          const run = check();
          const failure = run.parts.find(p => p.execution === "failed");
          assert.ok(failure, name);
          assert.match(failure.stderr, name === "occurrence" ? /unexpected fields/ : /wrong slice result/);
        }
        const damaged = new Store(join(work, "corrupt-slice"));
        process.env.TSCERT_STAGE_STORE = damaged.root;
        damaged.publishFinished("pass", entry.key, entry.result);
        const path = join(damaged.root, "entries", "pass", entry.key, "stdout");
        chmodSync(path, 0o644);
        writeFileSync(path, "wrong bytes");
        const repaired = check();
        assert.equal(repaired.slices.executed, units.length, "a bad payload digest misses");
        assert.deepEqual(repaired.parts.map(p => p.stdout.trimEnd()), worker(null).lines);

        process.env.TSCERT_STAGE_STORE = store.root;
        const bad: Ast = { ...ast, functions: [fn("bad", 10, number,
          { k: "lit", pos: [15, 16], lit: { a: "stringlit", v: "wrong" } })], init: [] };
        writeFileSync(fragment, JSON.stringify(bad));
        const located = check();
        assert.equal(located.slices.executed, 1);
        assert.match(located.parts[0]?.stdout ?? "", /"refusal"/);
        writeFileSync(fragment, moveSites(bad));
        const relocated = check();
        assert.equal(relocated.slices.executed, 1, "opaque diagnostics execute at current sites");
        assert.deepEqual(relocated.parts.map(p => p.stdout.trimEnd()), worker(null).lines, "the moved refusal's current diagnostic");

        const opaque: Ast = { ...bad, functions: [fn("bad", 10, number,
          { k: "id", pos: [15, 16], name: "missing[3,4)" })] };
        writeFileSync(fragment, moveSites(opaque));
        const quoted = check();
        assert.match(quoted.parts[0]?.stdout ?? "", /missing\[3,4\)/);
        assert.deepEqual(quoted.parts.map(p => p.stdout.trimEnd()), worker(null).lines);

        // A comment moves Box, its member annotation, a file-wide written
        // application, and the lexical location in a shadowing declarator.
        // An unrelated module cell and omitted mention also stay out of `read`.
        const declaration: DeclarationIdentity = { module: key, name: "Box", span: [3, 20] };
        const box: TypeTerm = { k: "reference", span: [32, 35], args: [],
          reference: { name: "Box", target: declaration, arguments: [], span: [32, 35] } };
        const definition: TypeDefinition = { declaration, parameters: [], bases: [], expression: {
          k: "object", fields: [{ name: "size", optional: false, readonly: true, type: number, span: [5, 15] }],
          calls: [], stringIndex: null, span: [4, 19],
        } };
        const wrapDecl: DeclarationIdentity = { module: key, name: "Wrap", span: [75, 95] };
        const wrapDef: TypeDefinition = { declaration: wrapDecl,
          parameters: [{ name: "T", span: [80, 81], defaulted: false }], bases: [],
          expression: { k: "object", fields: [{ name: "v", optional: false, readonly: true,
            type: { k: "parameter", index: 0, span: [88, 89] }, span: [85, 90] }],
            calls: [], stringIndex: null, span: [84, 92] } };
        const local = "item@4:7";
        const read: FunctionAst = { ...fn("read", 24, number, { k: "id", name: local, pos: [67, 71] }),
          params: [{ name: "box", type: box, pos: [28, 31] }],
          body: [{ k: "const", pos: [42, 60], bindings: [{ name: local, namePos: [46, 50], annot: null,
            early: false, init: { k: "read", field: "size", pos: [51, 59], e: { k: "id", name: "box", pos: [51, 54] } } }] },
            { k: "return", pos: [60, 72], e: { k: "id", name: local, pos: [67, 71] } }] };
        const original: Ast = { ...ast, init: [], omittedMentions: ["unrelated"], functions: [read],
          declarations: { ...ast.declarations,
            roots: [{ declaration, binding: { kind: "local", local: "Box", span: declaration.span } }],
            definitions: [definition, wrapDef],
            applications: [{ scope: [], reference: { name: "Wrap", target: wrapDecl, arguments: [[96, 99]], span: [91, 95] },
              parameters: [{ name: "T", span: [80, 81] }], args: [box],
              bounds: [{ k: "atom", name: "object", span: [82, 88] }], span: [91, 99], site: `${key}:1` }] } };
        writeFileSync(fragment, JSON.stringify(original));
        const firstRead = check();
        assert.equal(firstRead.slices.executed, 1);
        assert.match(firstRead.parts[0]?.stdout ?? "", /"key":"size"/);
        const movedOriginal: Ast = { ...original, omittedMentions: ["other"],
          init: [{ k: "let", pos: [101, 112], bindings: [{ name: "scratch", namePos: [105, 112], annot: null,
            early: true, init: { k: "alloc", pos: [115, 117], fields: [] } }] }] };
        writeFileSync(fragment, moveSites(movedOriginal).replaceAll(local, "item@5:7"));
        const movedRead = invokeWorker(verifierCall(verifierBuild, [...args.slice(0, -1), "read"], { TSCERT_SLICE_DRIVER: "1" }),
          fileWorkerProtocol, { limitMs: 60_000, force: false, recorder: null });
        assert.equal(movedRead.slices.executed, 0, "written applications, omittedMentions and unused module cells stay out of read's slice");
        assert.equal(movedRead.slices.replayed, 1);
        assert.deepEqual(movedRead.parts.map(p => p.stdout.trimEnd()), worker(null, "read").lines);

        // A non-binding initializer statement widens a module cell before a
        // constant reads it. Physical diagnostics keep all initializer statements.
        const stringType: TypeTerm = { k: "atom", name: "string", span: [3, 4] };
        const numOrStr: TypeTerm = { k: "union", parts: [number, stringType], span: [5, 6] };
        const initWidened: Ast = { ...ast,
          init: [
            { k: "let", pos: [10, 20], bindings: [{ name: "cell", namePos: [14, 18], annot: numOrStr, early: true,
              init: { k: "lit", pos: [19, 20], lit: { a: "numberlit", v: "1" } } }] },
            { k: "effect", pos: [21, 32], e: { k: "assign", pos: [21, 32], name: "cell", namePos: [21, 25],
              rhs: { k: "lit", pos: [28, 32], lit: { a: "stringlit", v: "oops" } } } },
            { k: "const", pos: [33, 48], bindings: [{ name: "saved", namePos: [39, 44], annot: null, early: false,
              init: { k: "id", pos: [45, 48], name: "cell" } }] },
          ],
          functions: [{ ...fn("badInit", 50, number, { k: "lit", pos: [80, 87], lit: { a: "stringlit", v: "wrong" } }),
            body: [
              { k: "const", pos: [55, 75], bindings: [{ name: "y", namePos: [61, 62], annot: number, early: false,
                init: { k: "id", pos: [68, 73], name: "saved" } }] },
              { k: "return", pos: [76, 88], e: { k: "lit", pos: [80, 87], lit: { a: "stringlit", v: "wrong" } } },
            ] }] };
        writeFileSync(fragment, JSON.stringify(initWidened));
        const widened = check();
        assert.deepEqual(widened.parts.map(p => p.stdout.trimEnd()), worker(null).lines);
        const badInitLine = must(widened.parts.find(p => p.part === "badInit@50")?.stdout, "badInit verdict");
        assert.match(badInitLine, /\[68,73\)/, "physical refusal reports the widened initializer read, not the later return");
        writeFileSync(fragment, moveSites(initWidened));
        const movedWidened = check();
        assert.deepEqual(movedWidened.parts.map(p => p.stdout.trimEnd()), worker(null).lines);
        const movedBadInit = must(movedWidened.parts.find(p => p.part === "badInit@150")?.stdout, "moved badInit verdict");
        assert.match(movedBadInit, /\[168,173\)/);

        const chain = (literal: string): Ast => ({ ...ast, init: [], functions: [
          fn("left", 10, number, { k: "lit", pos: [14, 15], lit: { a: "numberlit", v: literal } }),
          fn("middle", 30, number, callAt("left", 34)),
          fn("right", 50, number, callAt("middle", 54)),
        ] });
        writeFileSync(fragment, JSON.stringify(chain("1")));
        process.env.TSCERT_STAGE_STORE = join(work, "proposal-first");
        const profile = join(work, "resumed-checks");
        process.env.TSCERT_PROFILE = profile;
        const root = invokeWorker(verifierCall(verifierBuild, args, { TSCERT_SLICE_DRIVER: "1" }),
          { ...fileWorkerProtocol, parts: () => ["right@50"], request: () => JSON.stringify({ units: ["right@50"] }) }, { limitMs: 60_000, force: false, recorder: null });
        assert.equal(root.slices.proposalsExecuted, 2, "the two callees supply only proposals");
        assert.equal(root.slices.executed, 1);
        const completed = check();
        for (const part of completed.parts.filter(p => p.execution === "executed")) {
          const timings = readFileSync(join(profile, "work", part.record.attempt + ".jsonl"), "utf8");
          assert.doesNotMatch(timings, /"kind":"propose: member plans"/, "checking a saved proposal never settles it again");
        }
        assert.deepEqual(completed.parts.map(p => p.stdout.trimEnd()), worker(null).lines);
        assert.equal(completed.slices.executed, 2, "each callee checks at its saved proposal");
        writeFileSync(fragment, JSON.stringify(chain("2")));
        const edited = check();
        assert.equal(edited.slices.executed, 1, "only the edited callee checks");
        assert.equal(edited.slices.replayed, 2, "its equal stand-in cuts off both callers");
        assert.deepEqual(edited.parts.map(p => p.stdout.trimEnd()), worker(null).lines);

        // The written footprint is equal even when the definition fails
        // its return claim. The replayed caller retains that dependency.
        const declared = (e: Expr): Ast => ({ ...ast, init: [], functions: [
          { ...fn("left", 10, number, e), stated: emptyEffect.exits },
          ...chain("1").functions.slice(1),
        ] });
        writeFileSync(fragment, JSON.stringify(declared({ k: "lit", pos: [14, 15], lit: { a: "numberlit", v: "1" } })));
        check();
        const wrong = declared({ k: "lit", pos: [14, 15], lit: { a: "stringlit", v: "wrong" } });
        writeFileSync(fragment, JSON.stringify(wrong));
        const refused = check();
        assert.equal(refused.slices.executed, 1);
        assert.equal(refused.slices.replayed, 2);
        const [left, middle] = refused.parts.map(p => decodeVerdictLine(p.stdout.trimEnd()));
        assert.ok(left && "refusal" in left);
        assert.ok(middle && "accepted" in middle && middle.depends.includes("left@10"));
        writeFileSync(fragment, moveSites(wrong));
        const movedRefusal = check();
        assert.equal(movedRefusal.slices.executed, 1);
        assert.equal(movedRefusal.slices.replayed, 2);
        const physical = must(movedRefusal.parts[0], "the relocated refusal");
        const workTable = readFileSync(join(profile, "work", physical.record.attempt + ".jsonl"), "utf8");
        assert.doesNotMatch(workTable, /"kind":"slice: execute"/, "the relative refusal and its proposal replay");
        assert.match(workTable, /"kind":"slice: physical"/);
        assert.deepEqual(movedRefusal.parts.map(p => p.stdout.trimEnd()), worker(null).lines);
      } finally {
        writeFileSync(fragment, JSON.stringify(ast));
        if (beforeProfile === undefined) delete process.env.TSCERT_PROFILE;
        else process.env.TSCERT_PROFILE = beforeProfile;
        if (beforeStore === undefined) delete process.env.TSCERT_STAGE_STORE;
        else process.env.TSCERT_STAGE_STORE = beforeStore;
      }
    }
    const priorStore = process.env.TSCERT_STAGE_STORE;
    try {
      process.env.TSCERT_STAGE_STORE = join(work, "resume-" + variant);
      const options = { limitMs: 60_000, force: false, recorder: null };
      for (const storeDriver of [false, true]) {
        const call = verifierCall(verifierBuild, args, storeDriver ? { TSCERT_SLICE_DRIVER: "1" } : {});
        const first = invokeWorker(call, { ...fileWorkerProtocol, parts: () => half,
          request: () => JSON.stringify({ units: half }) }, options);
        assert.deepEqual(first.parts.map(p => p.execution), ["executed"]);
        const resumed = invokeWorker(call, fileWorkerProtocol, options);
        assert.equal(resumed.starts, 1);
        assert.equal(resumed.preparation.execution, "replayed");
        assert.deepEqual(resumed.parts.map(p => p.execution), units.map(u => half.includes(u) ? "replayed" : "executed"));
        assert.deepEqual(resumed.parts.map(p => p.stdout.trimEnd()), all.lines);
        if (storeDriver) {
          assert.equal(resumed.slices.proposalsExecuted, 0);
          assert.ok(resumed.slices.proposalsReplayed > 0, "the restarted worker reads the checked callee's proposals");
        }
      }
    } finally {
      if (priorStore === undefined) delete process.env.TSCERT_STAGE_STORE;
      else process.env.TSCERT_STAGE_STORE = priorStore;
    }
  }
});

control("probe settings leave the production verdict intact", async (): Promise<void> => {
  const artifacts = run("field-equality-union");
  const fragment = fragmentOf(artifacts);
  const interfaces = join(artifacts, "empty-interfaces.json");
  writeFileSync(interfaces, '{"modules":[]}');
  const args = ["--verify-interface-stage", "8", fragment, interfaces, sourceKey(artifacts), "12", ""];
  const plain = spawnSync(verifierBuild, args, { encoding: "utf8", env: {} });
  assert.equal(plain.status, 0, plain.stderr);
  const observed = spawnSync(verifierBuild, args, { encoding: "utf8", env: {
    TSCERT_FORCE: "start-facts", TSCERT_OBSERVE: "node:999999999",
  } });
  assert.equal(observed.status, plain.status, observed.stderr);
  assert.equal(observed.stdout, plain.stdout);
});

/** Install a verifier stand-in inside the control process and any worker it forks. */
function standInOptions(directory: string, stand: string): string[] {
  const adapter = pathToFileURL(join(root, "pipeline/stage-execution.mts")).href;
  const preload = join(directory, "stand-in.mjs");
  writeFileSync(preload, `import { mock } from "node:test";
import * as adapter from ${JSON.stringify(adapter)};
mock.module(${JSON.stringify(adapter)}, { exports: { ...adapter, verifier: ${JSON.stringify(stand)} } });
`);
  return ["--experimental-test-module-mocks", "--import", preload];
}

control("worker preparation over its limit: every unit recorded with its reason", async (): Promise<void> => {
  // The census's file run with the worker's preparation held past its limit
  // by a sleeping test worker: no unit has a verdict, and each
  // selected unit of the file is recorded with the preparation's timeout as
  // its reason.
  const work = runDirectory("single-pass-preparation-limit-");
  const driver = join(work, "driver.mts");
  const census = join(import.meta.dirname, "../dev/census.mts");
  const examples = join(import.meta.dirname, "../pipeline/examples");
  writeFileSync(driver, `
const { runFile, sourceModel } = await import(${JSON.stringify(census)});
const m = sourceModel(${JSON.stringify(examples)}, "evolving-bindings.ts");
const select = [...m.functions.keys()];
const run = await runFile(${JSON.stringify(examples)}, ${JSON.stringify(examples)}, () => m, m, select, new Map());
process.stdout.write(JSON.stringify({ select, units: run.units }));
process.exit(0);
`);
  const stand = join(work, "slow-worker.sh");
  writeFileSync(stand, `#!/bin/sh
for arg in "$@"; do
  if [ "$arg" = "--file-worker" ]; then exec sleep 30; fi
done
exec "${verifierBuild}" "$@"
`, { mode: 0o755 });
  const p = spawnSync(process.execPath, [...standInOptions(work, stand), driver], { encoding: "utf8", timeout: 170_000,
    env: { ...process.env, TSCERT_STEP_LIMIT: "3",
      TSCERT_STAGE_STORE: join(work, "store") } });
  assert.equal(p.status, 0, p.stderr);
  const out: unknown = JSON.parse(p.stdout);
  assert.ok(isObject(out) && Array.isArray(out.select) && Array.isArray(out.units), "the driver's record");
  const select: unknown[] = out.select, units: unknown[] = out.units;
  assert.ok(select.length >= 3, "a file of several functions");
  assert.deepEqual(units.map((u) => isObject(u) ? u.unit : null).sort(), [...select].sort(), "one unit per function");
  for (const u of units)
    assert.ok(isObject(u) && u.status !== "verified" && typeof u.detail === "string" &&
      u.detail.startsWith("no verdict: the file was refused before its units' checks: ") && /timeout/.test(u.detail),
      `a unit with the preparation's timeout as its reason: ${JSON.stringify(u)}`);
  say(`worker preparation over its limit: ${units.length} units recorded, each with the timeout`);
});

// ---------------------------------------------------------------------------
// Module interfaces: the store boundary of the interface stages.

infraControl("module interfaces: the store boundary", async (): Promise<void> => {
  const artifacts = run("certified-value-import");
  interfaceControls(fragmentOf(artifacts), join(artifacts, "interface-controls"), say, counted);
});

control("module interfaces: a forged row's entry term", async (): Promise<void> => {
  const artifacts = run("two-state-ensures-value-import");
  entryRowControl(fragmentOf(artifacts), join(artifacts, "entry-row-control"), say, counted);
});

control("module interfaces: a module's store stating no built-ins", async (): Promise<void> => {
  // A module document and its importer's each list `ArrayProto`, so both
  // stores state the built-ins and the store map relates them. A module
  // document with `ArrayProto` left out states none: no store map relates
  // its interface rows to the importer's store, and the unit reading the
  // import is refused at the read.
  const artifacts = run("certified-mts-value-import");
  accepted(pass(fragmentOf(artifacts)), "doubled@259", "the module's store stating the built-ins");
  const ast: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
  assert.ok(isObject(ast) && Array.isArray(ast.modules));
  let dropped = 0;
  const modules = ast.modules.map((m: unknown) => {
    assert.ok(isObject(m) && isObject(m.declarations) && Array.isArray(m.declarations.definitions));
    const definitions = m.declarations.definitions.filter((d: unknown) =>
      !(isObject(d) && isObject(d.declaration) && d.declaration.module === "tscert/array-prototype"));
    dropped += m.declarations.definitions.length - definitions.length;
    return { ...m, declarations: { ...m.declarations, definitions } };
  });
  assert.equal(dropped, 1, "scaled.mts's document lists ArrayProto");
  refused(pass(forged(artifacts, "forged-module-builtins", { ...ast, modules })), "doubled@259",
    "the module's store stating no built-ins",
    /source refusal at \[259,266\): signature rows differ: the import 'scaled', its module's interface rows refused by the store-map check/);
  say("a module's store stating no built-ins: the importer's read of it refused at the read");
});

control("module interfaces: rows of another signature", async (): Promise<void> => {
  // The importer and its module list their unique symbols in different
  // orders, and the rows agree at the symbols' canonical numbers. Interface
  // rows stating another signature are still refused at the read: `count`
  // returning `string` where the importer reads `number`, and the built-ins
  // keyed by a symbol number neither store gives a symbol.
  const artifacts = run("interface-rows-symbol-order-value-import");
  const fragment = fragmentOf(artifacts);
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  assert.ok(isObject(ast) && typeof ast.file === "string");
  const key = ast.file;
  const original: unknown = JSON.parse(readFileSync(join(artifacts, "interfaces", "interfaces.json"), "utf8"));
  const stage = (name: string, interfaces: unknown): Pass => {
    const path = join(artifacts, `${name}.json`);
    const text = JSON.stringify(interfaces);
    assert.ok(text !== undefined);
    writeFileSync(path, text);
    return passOf(counted(invokeProcess(verifierCall(verifierBuild, ["--subtype-rounds", "4096",
      "--verify-interface-stage", "8", fragment, path, key, "12", ""]), { limitMs: 60_000, force: false, recorder: null })));
  };
  accepted(stage("interfaces-as-published", original), "widest@912", "the published rows");
  const rowsOf = (j: unknown): { entry: Record<string, unknown>; rows: Record<string, unknown> } => {
    assert.ok(isObject(j) && Array.isArray(j.modules) && j.modules.length === 1);
    const m: unknown = j.modules[0];
    assert.ok(isObject(m) && Array.isArray(m.entries) && isObject(m.rows));
    const entry: unknown = m.entries[0];
    assert.ok(isObject(entry) && entry.name === "count");
    return { entry, rows: m.rows };
  };
  const at = /source refusal at \[912,918\): signature rows differ: the import 'count', its module's interface rows refused by the store-map check/;
  // `count`'s interface row, its results the table's `string` row.
  const strings: unknown = structuredClone(original);
  const { entry, rows } = rowsOf(strings);
  assert.ok(isObject(entry.established) && Array.isArray(entry.established.interface) && Array.isArray(rows.types));
  const types: unknown[] = rows.types;
  const string = types.findIndex((r) => JSON.stringify(r) === '["str"]');
  const at290 = entry.established.interface[0];
  assert.ok(string >= 0 && typeof at290 === "number");
  const row: unknown = types[at290];
  assert.ok(Array.isArray(row) && row.length === 1 && isObject(row[0]) && isObject(row[0].arrs));
  const arrs = row[0].arrs;
  assert.ok(Array.isArray(arrs.arrows) && Array.isArray(arrs.variadic));
  let results = 0;
  for (const a of [...arrs.arrows, ...arrs.variadic]) {
    assert.ok(isObject(a));
    a.result = [string];
    results++;
  }
  assert.ok(results > 0);
  refused(stage("interfaces-string-result", strings), "widest@912", "`count` returning `string`", at);
  // The built-ins' symbol keys, one renumbered to a number no store gives.
  const renumbered: unknown = structuredClone(original);
  const builtins = rowsOf(renumbered).rows.builtins;
  assert.ok(isObject(builtins) && Array.isArray(builtins.keys));
  const symbolKey = builtins.keys.findIndex((k: unknown) => isObject(k) && typeof k.symbol === "number");
  assert.ok(symbolKey >= 0);
  builtins.keys[symbolKey] = { symbol: 1 };
  refused(stage("interfaces-other-symbol", renumbered), "widest@912", "the built-ins keyed by another symbol", at);
  say("rows of another signature: a result of another type and a key of another symbol refused at the read");
});

control("module interfaces: a guard's promise rows forged", async (): Promise<void> => {
  // An imported guard's entry states its plain and promise signatures as
  // rows of its module's table. Rows stating another promise (another
  // parameter, an assertion's) or another promised type than the guard's
  // module established are refused at the importer's read, its store-map
  // check comparing them with the guard's declared type.
  const artifacts = run("guard-value-import");
  const fragment = fragmentOf(artifacts);
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  assert.ok(isObject(ast) && typeof ast.file === "string");
  const key = ast.file;
  const original: unknown = JSON.parse(readFileSync(join(artifacts, "interfaces", "interfaces.json"), "utf8"));
  const stage = (name: string, interfaces: unknown): Pass => {
    const path = join(artifacts, `${name}.json`);
    const text = JSON.stringify(interfaces);
    assert.ok(text !== undefined);
    writeFileSync(path, text);
    return passOf(counted(invokeProcess(verifierCall(verifierBuild, ["--subtype-rounds", "4096",
      "--verify-interface-stage", "8", fragment, path, key, "12", ""]), { limitMs: 60_000, force: false, recorder: null })));
  };
  accepted(stage("interfaces-as-published", original), "size@267", "the published rows");
  // Each promise signature of `isName`'s interface row, changed by `change`.
  const forge = (change: (signature: Record<string, unknown>, types: unknown[]) => void): unknown => {
    const forged: unknown = structuredClone(original);
    assert.ok(isObject(forged) && Array.isArray(forged.modules) && forged.modules.length === 1);
    const m: unknown = forged.modules[0];
    assert.ok(isObject(m) && Array.isArray(m.entries) && isObject(m.rows) && Array.isArray(m.rows.types));
    const types: unknown[] = m.rows.types;
    const entry: unknown = m.entries.find((e: unknown) => isObject(e) && e.name === "isName");
    assert.ok(isObject(entry) && isObject(entry.established) && Array.isArray(entry.established.interface));
    const root: unknown = entry.established.interface[0];
    assert.ok(typeof root === "number");
    const row: unknown = types[root];
    assert.ok(Array.isArray(row) && row.length === 1 && isObject(row[0]) && isObject(row[0].arrs));
    const arrs = row[0].arrs;
    assert.ok(Array.isArray(arrs.arrows) && Array.isArray(arrs.variadic));
    let promises = 0;
    for (const a of [...arrs.arrows, ...arrs.variadic]) {
      assert.ok(isObject(a) && isObject(a.effect));
      if (a.effect.promise === null) continue;
      change(a, types);
      promises++;
    }
    assert.ok(promises > 0, "isName's interface states a promise signature");
    return forged;
  };
  const at = /source refusal at \[\d+,\d+\): signature rows differ: the import 'isName', its module's interface rows refused by the store-map check/;
  const effectOf = (a: Record<string, unknown>): Record<string, unknown> => {
    assert.ok(isObject(a.effect));
    return a.effect;
  };
  refused(stage("interfaces-other-parameter", forge((a) => { effectOf(a).promise = { guards: { param: 1 } }; })),
    "size@267", "a promise about another parameter", at);
  refused(stage("interfaces-assertion", forge((a) => { effectOf(a).promise = { asserts: { param: 0 } }; })),
    "size@267", "an assertion's promise", at);
  refused(stage("interfaces-other-promised-type", forge((a, types) => {
    const number = types.findIndex((r) => JSON.stringify(r) === '["num"]');
    assert.ok(number >= 0);
    a.result = [number];
  })), "size@267", "another promised type", at);
  say("a guard's promise rows forged: another parameter, an assertion and another promised type refused at the read");
});

// ---------------------------------------------------------------------------
// Forged fragments: the parser's document forged, refused by the pass.

/** A case's fragment, parsed. */
const fragmentAst = (artifacts: string): Ast => readFragmentFile(fragmentOf(artifacts));
/** The unit of the function `name` of a fragment: `name@<its name's position>`. */
function unitOf(ast: Ast, name: string): string {
  const fn = must(ast.functions.find((f) => f.name === name), `function ${name}`);
  return `${name}@${fn.namePos[0]}`;
}
/** Visit every object of a parsed value, children first. */
function visitAll(value: unknown, at: (node: Record<string, unknown>) => void): void {
  if (Array.isArray(value)) { for (const child of value) visitAll(child, at); return; }
  if (!isObject(value)) return;
  for (const child of Object.values(value)) visitAll(child, at);
  at(value);
}

/** The honest baseline of a forged-fragment control: the case's `unit`
 * accepted unforced. */
function honest(file: string, unit: string, p: Pass = pass(fragmentOf(run(file)))): void {
  accepted(p, unit, `${file} honest`);
}

control("forged fragment: an incompatible heritage type argument on super", async (): Promise<void> => {
  const file = "class-generic-inheritance";
  const artifacts = run(file);
  honest(file, "init");
  const ast = fragmentAst(artifacts);
  const source = readFileSync(join(root, "pipeline/examples", `${file}.ts`), "utf8");
  const superPos = source.indexOf("super(value)");
  assert.ok(superPos >= 0);
  let changed = 0;
  visitAll(ast.init, (node) => {
    if (node.k !== "new" || !Array.isArray(node.pos) || node.pos[0] !== superPos) return;
    assert.ok(Array.isArray(node.typeArgs) && node.typeArgs.length === 1 &&
      isObject(node.typeArgs[0]) && node.typeArgs[0].name === "number");
    node.typeArgs = [{ ...node.typeArgs[0], name: "string" }];
    changed++;
  });
  assert.equal(changed, 1);
  refused(pass(forged(artifacts, "forged-super-type-argument", ast)), "init",
    "a numeric super argument at a string heritage type",
    new RegExp(`source expression obligation at \\[${superPos},.*no derivation of its node-typing claim`));

  const bounded = fragmentAst(artifacts);
  changed = 0;
  visitAll(bounded.init, (node) => {
    if (node.k !== "new" || !isObject(node.callee) || node.callee.name !== "Tagged.[[class]]") return;
    assert.ok(Array.isArray(node.typeArgs) && isObject(node.typeArgs[0]));
    assert.ok(Array.isArray(node.args) && isObject(node.args[0]));
    node.typeArgs = [{ k: "atom", name: "string", span: node.typeArgs[0].span }];
    node.args = [{ k: "lit", lit: { a: "stringlit", v: "wrong" }, pos: node.args[0].pos }];
    changed++;
  });
  assert.equal(changed, 1);
  refused(pass(forged(artifacts, "forged-super-bound", bounded)), "init",
    "a heritage type argument outside the base's bound", /the claimed type is not a checked constructor instance/);
});

control("forged fragment: reversed tuple positions on super", async (): Promise<void> => {
  const file = "class-generic-inheritance-pack";
  const artifacts = run(file);
  honest(file, "init");
  const ast = fragmentAst(artifacts);
  let position: number | undefined;
  visitAll(ast.init, (node) => {
    if (node.k !== "new" || !isObject(node.callee) ||
        node.callee.name !== "CallbackBase.[[class]]" || !Array.isArray(node.typeArgs)) return;
    const argument = node.typeArgs[0];
    if (!isObject(argument) || argument.k !== "tuple") return;
    assert.equal(position, undefined);
    assert.ok(Array.isArray(node.pos) && typeof node.pos[0] === "number");
    assert.ok(Array.isArray(argument.required) && argument.required.length === 2);
    position = node.pos[0];
    argument.required = [argument.required[1], argument.required[0]];
  });
  assert.ok(position !== undefined);
  refused(pass(forged(artifacts, "forged-super-tuple", ast)), "init",
    "a tuple callback with the opposite heritage argument order",
    new RegExp(`source expression obligation at \\[${position},.*no derivation of its node-typing claim`));
});

control("forged fragment: a false bound in a Boolean postcondition", async (): Promise<void> => {
  const artifacts = run("pretext-clause-postcondition");
  const ast = fragmentAst(artifacts);
  const unit = unitOf(ast, "advance");
  honest("pretext-clause-postcondition", unit);
  must(ast.functions.find((f) => f.name === "advance"), "advance").ensures.push({ guarded: { slot: 0, path: [], tag: "false",
    body: { linear: { fact: { le: { form: [[{ kind: "value", slot: 3, path: ["index"] }, 1]], bound: -1 } } } } } });
  refused(pass(forged(artifacts, "forged-boolean-postcondition", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("Boolean postconditions: a false bound under a true return is refused at the return");
});

control("forged fragment: a quantified precondition removed", async (): Promise<void> => {
  const artifacts = run("bounds-quantified-invariant");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "read"), "read's contract");
  assert.ok(fn.requires.some((f) => "every" in f));
  honest("bounds-quantified-invariant", unitOf(ast, "read"));
  fn.requires = [];
  refused(pass(forged(artifacts, "without-quantified-precondition", ast)), unitOf(ast, "read"), "forged");
  say("bounds: the fragment without its quantified precondition refused");
});

control("forged fragment: a false loop-cell invariant", async (): Promise<void> => {
  const artifacts = run("bounds-cell-invariant");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "walk"), "walk's body");
  const unit = unitOf(ast, "walk");
  honest("bounds-cell-invariant", unit);
  visitAll(fn.body, (value) => {
    if (value.k === "while" && isObject(value.invariant) && Array.isArray(value.invariant.facts))
      value.invariant.facts.push({ linear: { fact: { le: { form: [], bound: -1 } } } });
  });
  refused(pass(forged(artifacts, "false-cell-invariant", ast)), unit, "forged");
  say("bounds: a false cell invariant written into the loop refused");
});

control("forged fragment: a closure's written precondition removed", async (): Promise<void> => {
  const artifacts = run("closure-precondition");
  const ast = fragmentAst(artifacts);
  const unforced = pass(fragmentOf(artifacts));
  visitAll(ast, (value) => {
    if (value.k === "lambda") value.requires = [];
  });
  const p = pass(forged(artifacts, "closure-without-precondition", ast));
  const lost = [...unforced.verdicts].filter(([u, v]) => v.closed && p.verdicts.get(u)?.closed !== true).map(([u]) => u);
  assert.ok(lost.length > 0 || p.status !== 0 && p.verdicts.size === 0, `forged: no unit refused: ${words(p).slice(0, 2000)}`);
  say(`closures: the fragment without the closure's written precondition refused (${lost.join(", ") || "the front"})`);
});

/** A function's statement forged in the fragment: `stated` replaced by the
 * exits of a written frame (`statedExits`). */
type Stated = NonNullable<Ast["functions"][number]["stated"]>;
/** The spine regions a statement's normal frame states. */
const statedRegions = (stated: Stated): SpineRegion[] => stated.normal.frame.flatMap(({ region, change }) =>
  typeof region === "object" && "path" in region && region.path.key === "[]" && change === "any"
    ? [{ position: region.path.x, path: [...region.path.fields], key: "[]", change: "any" as const }] : []);
function forgedStatement(artifacts: string, name: string, document: string, stated: StatedFrame,
    expected?: SpineRegion[]): Pass {
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === name), name);
  if (expected === undefined) assert.equal(fn.stated, null, `${name} states nothing`);
  else assert.deepEqual(fn.stated === null ? null : statedRegions(fn.stated), expected, `${name}'s regions`);
  fn.stated = statedExits(stated);
  return pass(forged(artifacts, document, ast));
}

control("forged fragment: a fresh result stated of an identity function", async (): Promise<void> => {
  const artifacts = run("stated-fresh");
  const unit = unitOf(fragmentAst(artifacts), "same");
  honest("stated-fresh", unit);
  refused(forgedStatement(artifacts, "same", "forged-fresh-fragment",
    { footprint: { value: "any", spine: "any" }, onThrow: false, fresh: true, regions: [] }), unit, "forged");
  say("forged fresh result: an identity function's statement forged to promise a fresh result, refused at its unit");
});

control("forged fragment: a fraction's result forged to SafeInt", async (): Promise<void> => {
  const artifacts = run("safe-int");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "third"), "third");
  const unit = unitOf(ast, "third");
  honest("safe-int", unit);
  assert.ok(fn.retType.k === "atom" && fn.retType.name === "number", "third's result is a number");
  fn.retType = { ...fn.retType, name: "safeInt" };
  refused(pass(forged(artifacts, "forged-safe-int-result", ast)), unit, "forged", /return-contract|return at node/);
  say("forged SafeInt: a fraction's result forged from `number` to the safe integers, refused at its return");
});

control("forged fragment: an index parameter forged to SafeInt", async (): Promise<void> => {
  const artifacts = run("safe-int-index");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "readAt"), "readAt");
  const unit = unitOf(ast, "middle");
  honest("safe-int-index", unit);
  const i = must(fn.params[1], "readAt's index");
  assert.ok(i.type?.k === "atom" && i.type.name === "number", "readAt's index is a number");
  i.type = { ...i.type, name: "safeInt" };
  refused(pass(forged(artifacts, "forged-safe-int-parameter", ast)), unit, "forged",
    /its operands. claims are function, array, number; its claim is number/);
  say("forged SafeInt: an index parameter forged from `number` to the safe integers, refused at the call passing a fraction");
});

control("forged fragment: Number.isSafeInteger's integer fact removed", async (): Promise<void> => {
  const artifacts = run("safe-int-is-safe-integer");
  const ast = fragmentAst(artifacts);
  const unit = unitOf(ast, "asInt");
  honest("safe-int-is-safe-integer", unit);
  const number = must(ast.declarations.definitions.find((d) => d.declaration.name === "Number"), "Number");
  const expression = number.expression;
  assert.ok(expression !== null && expression.k === "object", "Number's type is an object");
  const member = must(expression.fields.find((f) => f.name === "isSafeInteger"), "isSafeInteger");
  const type = member.type;
  assert.ok(type.k === "function" && type.effect.exits.normal.ensures.length > 0, "isSafeInteger states its fact");
  member.type = { ...type, effect: { ...type.effect, exits: { ...type.effect.exits,
    normal: { ...type.effect.exits.normal, ensures: [] } } } };
  refused(pass(forged(artifacts, "forged-is-safe-integer-fact", ast)), unit, "forged",
    /its operands. claims are number; its claim is SafeInt/);
  say("forged int fact: Number.isSafeInteger stating no fact of its argument, its true branch's binding at SafeInt refused");
});

control("forged fragment: a return's integer fact removed", async (): Promise<void> => {
  const artifacts = run("safe-int-arith-field");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "next"), "next");
  const unit = unitOf(ast, "next");
  honest("safe-int-arith-field", unit);
  assert.equal(fn.requires.length, 2, "next states its range");
  fn.requires = fn.requires.slice(0, 1);
  refused(pass(forged(artifacts, "forged-safe-int-return-range", ast)), unit, "forged",
    /its operands. claims are number; its claim is SafeInt/);
  say("forged refinement at a return: `n + 1` with no upper bound on `n`, its return at SafeInt refused");
});

control("forged fragment: spine regions moved", async (): Promise<void> => {
  const artifacts = run("stated-argument-store");
  const ast = fragmentAst(artifacts);
  const trim = unitOf(ast, "trim"), shrink = unitOf(ast, "shrink");
  const unforced = pass(fragmentOf(artifacts));
  honest("stated-argument-store", trim, unforced);
  honest("stated-argument-store", shrink, unforced);
  refused(forgedStatement(artifacts, "trim", "forged-region-fragment",
    { footprint: { value: "any", spine: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path: [], key: "[]", change: "any" }] },
    [{ position: 2, path: [], key: "[]", change: "any" }]), trim, "trim's region at n");
  const ownAst = fragmentAst(artifacts);
  must(ownAst.functions.find((f) => f.name === "shrink"), "shrink").stated =
    statedExits({ footprint: { value: "any", spine: "keep" }, onThrow: false, fresh: false, regions: [{ position: 0, path: [], key: "[]", change: "any" }] });
  refused(pass(forged(artifacts, "forged-receiver-region-fragment", ownAst)), shrink, "shrink's region at the receiver");
  say("forged spine regions: a region moved to another parameter, and one at an undeclared receiver, each refused at its unit");
});

control("forged fragment: path regions moved", async (): Promise<void> => {
  const artifacts = run("stated-argument-path");
  const unit = unitOf(fragmentAst(artifacts), "readRuns");
  honest("stated-argument-path", unit);
  const moved: { document: string; path: string[] }[] = [{ document: "forged-path-region-fragment", path: [] },
    { document: "forged-path-field-fragment", path: ["closed"] }];
  for (const { document, path } of moved)
    refused(forgedStatement(artifacts, "readRuns", document,
      { footprint: { value: "any", spine: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path, key: "[]", change: "any" }] },
      [{ position: 1, path: ["openBrackets"], key: "[]", change: "any" }]), unit, document);
  say("forged path regions: a path region moved to its record's own spine, and one through a field the type does not state, refused at the unit");
});

control("forged fragment: rebased regions", async (): Promise<void> => {
  const steps = run("stated-region-steps");
  const scan = unitOf(fragmentAst(steps), "scan");
  honest("stated-region-steps", scan);
  refused(forgedStatement(steps, "scan", "forged-rebased-fragment",
    { footprint: { value: "any", spine: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path: [], key: "[]", change: "any" }] },
    [{ position: 1, path: ["open"], key: "[]", change: "any" }]), scan, "scan's region at its record");
  const nullable = run("stated-region-nullable-write");
  const mark = unitOf(fragmentAst(nullable), "mark");
  honest("stated-region-nullable-write", mark);
  refused(forgedStatement(nullable, "mark", "forged-witness-fragment",
    { footprint: { value: "any", spine: "keep" }, onThrow: false, fresh: false, regions: [{ position: 2, path: ["open"], key: "[]", change: "any" }] },
    [{ position: 1, path: ["open"], key: "[]", change: "any" }]), mark, "mark's region through a number");
  say("forged rebasing: a caller's region moved from the field's array to its record, and a region through a number parameter, each refused at its unit");
});

control("forged fragment: a fresh result whose spine a caller pops", async (): Promise<void> => {
  const artifacts = run("invalid-stated-region-fresh-call");
  const unit = unitOf(fragmentAst(artifacts), "same");
  honest("invalid-stated-region-fresh-call", unit);
  refused(forgedStatement(artifacts, "same", "forged-fresh-call-fragment",
    { footprint: { value: "any", spine: "any" }, onThrow: false, fresh: true, regions: [] }), unit, "forged");
  say("forged fresh spine: a fresh result forged onto a function returning its parameter refused at the function's unit");
});

control("forged fragment: an old array at a slot's join", async (): Promise<void> => {
  const artifacts = run("stated-slot-collect");
  const ast = fragmentAst(artifacts);
  const unit = unitOf(ast, "collect");
  honest("stated-slot-collect", unit);
  let replaced = 0;
  visitAll(ast, (node) => {
    const rhs = node.rhs;
    if (node.k === "nullishAssign" && node.name === "acc" && isObject(rhs) && rhs.k === "arrayLit") {
      replaced++;
      node.rhs = { k: "id", pos: rhs.pos, name: "xs" };
    }
  });
  assert.equal(replaced, 1, "one `acc ??= []`");
  refused(pass(forged(artifacts, "forged-slot-join-fragment", ast)), unit, "forged");
  say("forged slot join: an old array on the nullish path of `acc ??= …`, refused at its unit");
});

control("forged fragment: a loop invariant's entry term at another call position", async (): Promise<void> => {
  // `atEntry` names the entry state's namespace: the term's slot is a call
  // position of the function's entry frame, read there whatever the loop's
  // current bindings are. Moved to `from`'s position, the invariant states
  // the length of a number's field, which no edge establishes; moved past the
  // frame, the lowering refuses it.
  const artifacts = run("two-state-invariant-after-statement");
  const unit = unitOf(fragmentAst(artifacts), "measure");
  honest("two-state-invariant-after-statement", unit);
  const moved = (to: number, name: string): string => {
    const ast = fragmentAst(artifacts);
    let entries = 0;
    visitAll(must(ast.functions.find((f) => f.name === "measure"), "measure").body, (value) => {
      if (value.atEntry === true && typeof value.slot === "number") { value.slot = to; entries++; }
    });
    assert.ok(entries > 0, "the loop invariant's entry term");
    return forged(artifacts, name, ast);
  };
  refused(pass(moved(1, "entry-term-at-from")), unit, "forged");
  refused(pass(moved(9, "entry-term-past-frame")), unit, "forged", /reads in the entry state a position the function's entry frame does not hold/);
  say("two-state invariants: an entry term moved to another call position or past the entry frame, refused");
});

control("forged fragment: a false postcondition", async (): Promise<void> => {
  const artifacts = run("type-invariant-walker");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "countBreaks"), "countBreaks");
  const unit = unitOf(ast, "countBreaks");
  honest("type-invariant-walker", unit);
  assert.ok(fn.ensures.every((f) => !JSON.stringify(f).includes('"slot":0')), "countBreaks states no result fact");
  fn.ensures = [...fn.ensures, { int: { slot: 0 } },
    { linear: { fact: { le: { form: [[{ kind: "value", slot: 0, path: [] }, 1]], bound: -1 } } } }];
  refused(pass(forged(artifacts, "forged-ensures-fragment", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("type invariants: a postcondition forged into the document, refused at the return");
});

control("forged fragment: a false parameter fact at the returns", async (): Promise<void> => {
  const artifacts = run("cursor-invariant-after-writing-call");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "step"), "step");
  const unit = unitOf(ast, "step");
  honest("cursor-invariant-after-writing-call", unit);
  fn.ensures = [...fn.ensures,
    { linear: { fact: { le: { form: [[{ kind: "value", slot: 3, path: ["segmentIndex"] }, 1]], bound: -1 } } } }];
  refused(pass(forged(artifacts, "forged-parameter-ensures-fragment", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("type invariants: a parameter's fact at the returns forged into the document, refused at a return");
});

control("omitted units: escapes in omitted code", async (): Promise<void> => {
  for (const file of ["invalid-module-cache-omitted-default", "invalid-module-cache-omitted-let"]) {
    using outcome = checkSource(join(root, "pipeline/examples", `${file}.ts`), undefined, false, undefined, true,
      { omitted: ["leak"], select: null });
    assert.ok(outcome.status === "unverified" || outcome.status === "unsupported", `${file}: ${outcome.status}`);
    assert.match(outcome.detail, /write/, `${file}: ${outcome.detail.slice(0, 600)}`);
  }
  say("module cache: escapes in omitted code keep the cache's write refused");
});

const enumMembers = new Map<string, string>([["SyntaxKind", "Identifier"], ["NodeFlags", "Const"], ["TypeFlags", "Union"],
  ["SymbolFlags", "Alias"], ["SignatureKind", "Call"], ["ElementFlags", "Required"], ["DiagnosticCategory", "Error"],
  ["TypePredicateKind", "Identifier"]]);
for (const reexport of [false, true]) for (const mismatched of [false, true])
  control(`compiler enum binding, ${reexport ? "re-exported" : "direct"}, ${mismatched ? "mismatched" : "audited"}`, async (): Promise<void> => {
    const audited = resolve(root, "tools/node_modules/typescript");
    const dir = runDirectory("tscert-compiler-enum-binding-");
    const installed = join(dir, "node_modules", "typescript");
    mkdirSync(join(dir, "node_modules"));
    const member = (name: string): string => must(enumMembers.get(name), `a member of ${name}`);
    if (mismatched) {
      mkdirSync(installed);
      writeFileSync(join(installed, "package.json"), JSON.stringify({ name: "typescript", type: "module",
        exports: { "./unstable/ast": "./enums.js", "./unstable/sync": "./enums.js" } }));
      writeFileSync(join(installed, "enums.js"), hostEnums.map(({ name }) =>
        `export const ${name} = { ${member(name)}: -123 };`).join("\n"));
    } else symlinkSync(audited, installed);
    writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
      module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
      allowImportingTsExtensions: true, paths: {
        "typescript/unstable/ast": [join(audited, "dist/ast/index.d.ts")],
        "typescript/unstable/sync": [join(audited, "dist/api/sync/api.d.ts")],
      } }, include: ["*.ts"] }));
    for (const { name } of hostEnums) {
      const entry = name === "SyntaxKind" || name === "NodeFlags" ? "ast" : "sync";
      writeFileSync(join(dir, "barrel.ts"), `export { ${name} as Enum } from "typescript/unstable/${entry}";\n`);
      const file = join(dir, "value.ts");
      writeFileSync(file, `import { ${reexport ? "Enum" : name + " as Enum"} } from "${reexport ? "./barrel.ts" : "typescript/unstable/" + entry}";\nexport function value(): Enum.${member(name)} { return Enum.${member(name)}; }\n`);
      using outcome = checkSource(file, tsconfigOf(dir), false, undefined, true);
      assert.equal(outcome.status, mismatched ? "unsupported" : "verified", `${name}, reexport=${reexport}: ${JSON.stringify(outcome)}`);
      if (outcome.status !== "verified") {
        assert.match(outcome.detail, /the host enum/);
        const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
          `import { value } from ${JSON.stringify(pathToFileURL(file).href)}; console.log(value());`], { encoding: "utf8", cwd: dir });
        assert.equal(ran.status, 0, ran.stderr);
        assert.equal(ran.stdout.trim(), "-123", `${name}: Node returns the other installation's value`);
      }
    }
    say(`compiler enum binding, ${reexport ? "re-exported" : "direct"}: all ${hostEnums.length} enums, ${mismatched ? "mismatched bindings refused and counterexamples executed under Node" : "audited bindings verified"}`);
  });

control("forged fragment: malformed bodies", async (): Promise<void> => {
  const good = run("stateful-source/arithmetic");
  const source = fragmentAst(good);
  const fn = must(source.functions[0], "a function");
  const undef = { k: "lit", pos: [1, 3], lit: { a: "undefined" } };
  const effect = (e: object): object => ({ k: "effect", pos: [1, 3], e });
  const malformed: [unknown[], RegExp][] = [
    [[effect({ k: "unary", pos: [1, 3], op: "invalid", e: undef }), ...fn.body], /unknown unary operator 'invalid'/],
    [[effect({ k: "typeofTest", pos: [1, 3], shape: "invalid", equal: true, e: undef }), ...fn.body],
      /unsupported typeof test 'invalid'/],
    [[effect({ k: "futureExpression", pos: [1, 3], e: undef }), ...fn.body],
      /unsupported source expression at \[1,3\): expression outside the stateful fragment/],
    [[{ k: "break", pos: [1, 3], label: null }], /break or continue outside a source loop/],
  ];
  for (const [i, [body, refusal]] of malformed.entries())
    refusedFile(pass(forged(good, `planning-boundaries-${i}`, { ...source, functions: [{ ...fn, body }] })), `malformed ${i}`, refusal);
  say("malformed bodies: an unknown operator, typeof shape, expression kind and a break without a target, each refused by its own refusal");
});

control("forged fragment: a deferred mapped type", async (): Promise<void> => {
  const good = run("mapped-identity-named");
  const source = fragmentAst(good);
  const viewed = source.functions.find((f) => f.name === "viewed");
  const [param] = viewed?.params ?? [];
  assert.ok(viewed && param && param.type.k === "reference", "viewed takes a Shape");
  const deferred = deferredIdentity({ object: param.type, homomorphic: true, readonlyMod: "add", optionalMod: "keep", exact: null },
    { k: "atom", name: "never", span: param.type.span }, param.type.span);
  const atParameter = { ...source, functions: source.functions.map((f) => f !== viewed ? f
    : { ...f, params: [{ ...param, type: deferred }] }) };
  const atDefinition = { ...source, declarations: { ...source.declarations,
    definitions: source.declarations.definitions.map((d) => d.declaration.name === "Copy" ? { ...d, expression: deferred } : d) } };
  for (const [name, document] of [["parameter", atParameter], ["definition", atDefinition]] as const)
    refusedFile(pass(forged(good, `deferred-identity-${name}`, document)), name, /reference has no declaration equation/);
  say("a deferred mapped type in a forged parser document, at a parameter and at a definition: refused");
});

control("forged fragment: graph labels, claim-shaped annotations, unexamined fields", async (): Promise<void> => {
  const good = run("values");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(good), "utf8"));
  assert.ok(isObject(fragment));
  for (const [i, [retType, refusal]] of ([
    [{ a: "graph", label: 4 }, /source cannot state an internal graph label/],
    [{ top: false, atoms: [{ a: "boolean" }] }, /a source annotation is a type term, not a claim/],
  ] as const).entries()) {
    const document = structuredClone(fragment);
    assert.ok(Array.isArray(document.functions) && isObject(document.functions[0]) && "retType" in document.functions[0]);
    Object.assign(document.functions[0], { retType });
    refusedFile(pass(forged(good, `raw-graph-annotation-${i}`, document)), `retType ${i}`, refusal);
  }
  refusedFile(pass(forged(good, "extra-ast-field", { ...fragment, unexamined: true })), "root field", /unexpected fields/);
  for (const kind of ["id", "return"]) {
    const nested = structuredClone(fragment);
    const mark = (node: unknown): boolean => {
      if (Array.isArray(node)) return node.some(mark);
      if (!isObject(node)) return false;
      if (node.k === kind) {
        Object.assign(node, { unexamined: true });
        return true;
      }
      return Object.values(node).some(mark);
    };
    assert.ok(mark(nested), kind);
    refusedFile(pass(forged(good, `extra-${kind}-field`, nested)), `${kind} field`, /unexpected fields/);
  }
  say("a graph label, a claim-shaped annotation and an unexamined field in the parser's document, at its root or on a node: refused");
});

control("forged fragment: overload units at another function's code", async (): Promise<void> => {
  const artifacts = run("overloaded-function");
  const ast = fragmentAst(artifacts);
  const units = ast.functions.filter((f) => f.name === "pick");
  assert.equal(units.length, 2, "pick's overload units");
  must(units[1], "pick's second unit").body = must(ast.functions.find((f) => f.name === "count"), "count").body;
  refusedFile(pass(forged(artifacts, "forged-overload-code", ast)), "forged", /the units of pick are no overloads of one declaration's code/);
  say("overload units forged at another function's code: refused");
});

control("forged fragment: a module's document leaving out a function an import reaches", async (): Promise<void> => {
  // The module document is the front's: a source cannot leave a function
  // out of it. An import whose module's document binds no name a read of it
  // reaches refuses each unit reading the import (`--verify-interface-stage`):
  // a function the import's code calls (`describe`, which `label` reads),
  // and the imported function itself (`label`).
  const certified = run("certified-value-import");
  for (const name of ["describe", "label"]) {
    const ast = fragmentAst(certified);
    const module = must(ast.modules.find((m) => m.location.endsWith("certified.ts")), "certified.ts's module");
    assert.ok(module.functions.some((f) => f.name === name), `certified.ts's ${name}`);
    module.functions = module.functions.filter((f) => f.name !== name);
    const path = forged(certified, `forged-absent-${name}`, ast);
    const at = new RegExp(`source refusal at \\[\\d+,\\d+\\): unbound name ${name} in \\./certified\\.ts, read through the import 'label'`);
    const p = pass(path);
    refused(p, "labels@744", `${name} absent`, at);
    for (const unit of ["doubled@658", "tallies@829", "values@937", "innerValues@1032"])
      accepted(p, unit, `${name} absent, a unit not reading label`);
  }
  say("a module's document leaving out a function an import reaches (the imported one, or one it calls): the units reading the import refused at the read");
});

control("forged fragment: unbound names", async (): Promise<void> => {
  // A read renamed to a name nothing binds: a spread argument's operand and an assignment's target.
  // `located`: the refusal names a span holding the identifier; else (the
  // front's refusal of an assignment, which states no span) it names it.
  const unboundAt = (file: string, marker: string, skip: number, k: string, name: string, located: boolean): void => {
    const artifacts = run(file);
    const text = readFileSync(join(root, "pipeline/examples", `${file}.ts`), "utf8");
    const at = text.indexOf(marker) + skip;
    const document: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
    let renamed = 0;
    visitAll(document, (node) => {
      const pos = k === "assign" ? node.namePos : node.pos;
      if (node.k === k && node.name === name && Array.isArray(pos) && pos[0] === at) {
        renamed++;
        node.name = "missing";
      }
    });
    assert.equal(renamed, 1, `${file}: one ${k} node naming ${name} at ${at}`);
    assert.ok(isObject(document));
    const p = pass(forged(artifacts, `forged-unbound-${k}`, document));
    refusedFile(p, `${file} ${k}`);
    // Refused at a span holding the identifier.
    const spans = [...words(p).matchAll(/at \[(\d+),(\d+)\)/g)].map((m) => [Number(m[1]), Number(m[2])]);
    if (located) assert.ok(spans.some(([a, b]) => a <= at && at < b), `${file} ${k}: no refusal located at ${at}: ${words(p).slice(0, 1500)}`);
    else assert.match(words(p), /'missing'/, `${file} ${k}`);
  };
  unboundAt("array-readable", "...source", "...".length, "id", "source", true);
  unboundAt("assignment-effects", "(state = 1)", "(".length, "assign", "state", false);
  say("a read of a name its document does not bind, a spread operand's and an assignment target's: refused at a span holding it");
});

control("forged fragment: binder roles, an unguarded alias, written applications", async (): Promise<void> => {
  const span: [number, number] = [0, 0];
  const binder = (name: string): TypeTerm => ({ k: "binder", name, span });
  const method = (params: TypeTerm[], rest: TypeTerm | null, result: TypeTerm): Extract<TypeTerm, { k: "function" }> =>
    ({ k: "function", effect: ordinaryEffect, receiver: { k: "self", span }, params, rest, result, span });
  const scheme = (name: string, signature: Extract<TypeTerm, { k: "function" }>,
      bound: TypeTerm | null = null): TypeTerm =>
    ({ k: "scheme", binders: [{ name, bound, default: null, resolution: null, span }], signatures: [signature], span });
  const runner = (inner: TypeTerm): TypeTerm => scheme("P", method(
    [{ k: "object", fields: [{ name: "id", optional: false, readonly: true, type: inner, span }],
      stringIndex: null, calls: [], span }],
    { k: "pack", of: binder("P"), span }, { k: "atom", name: "number", span }),
    { k: "array", presence: "readable", readonly: false, element: { k: "atom", name: "unknown", span }, span });
  const forgeDocument = (file: string, name: string, change: (fragment: Ast) => void): Pass => {
    const artifacts = run(file);
    const fragment = fragmentAst(artifacts);
    change(fragment);
    return pass(forged(artifacts, name, fragment));
  };
  const forgeDefinition = (file: string, definition: string, name: string, change: (d: TypeDefinition) => void): Pass =>
    forgeDocument(file, name, (fragment) =>
      change(must(fragment.declarations.definitions.find((d) => d.declaration.name === definition), definition)));
  const withRun = (inner: TypeTerm) => (d: TypeDefinition): void => {
    assert(d.expression?.k === "object");
    must(d.expression.fields[0], "Runner's method").type = runner(inner);
  };
  const acceptedFile = (p: Pass, what: string): void =>
    assert.ok(p.status === 0 && [...p.verdicts.values()].every((v) => v.closed), `${what}: refused: ${words(p).slice(0, 1500)}`);
  acceptedFile(pass(fragmentOf(run("scheme-binder-roles"))), "scheme-binder-roles honest");
  acceptedFile(forgeDefinition("scheme-binder-roles", "Runner", "forged-shadowed-pack",
    withRun(scheme("P", method([binder("P")], null, binder("P"))))), "a nested binder shadowing the pack");
  refusedFile(forgeDefinition("scheme-binder-roles", "Runner", "forged-mixed-pack",
    withRun(scheme("Q", method([binder("Q"), binder("P")], null, binder("Q"))))), "a binder as value and pack",
    /Runner: generic contract at \[0,0\]: a binder used as both a value and an argument pack is not represented/);
  refusedFile(forgeDefinition("non-regular-alias", "Box", "forged-unguarded-alias", (d) => {
    assert(d.expression?.k === "object");
    const next = must(d.expression.fields.find((f) => f.name === "next"), "Box's next").type;
    assert(next.k === "union");
    d.expression = { k: "union", parts: [{ k: "parameter", index: 0, span }, must(next.parts[0], "Box<[T]>")], span };
  }), "unguarded alias",
  /unguarded alias cycle through Box: a recursive alias must reach itself through an object, array, tuple or function type/);
  const dependent = (fragment: Ast): Ast["declarations"]["applications"][number] =>
    must(fragment.declarations.applications.find((a) => a.site.endsWith("#dependent")), "dependent's B<U>");
  refusedFile(forgeDocument("written-scopes", "forged-written-argument", (fragment) => {
    dependent(fragment).args = [{ k: "atom", name: "number", span }];
  }), "a written argument", /a written application: the type argument for B's "T" .*does not establish its declared bound: number ≤ string/);
  refusedFile(forgeDocument("written-scopes", "forged-written-scope", (fragment) => {
    for (const level of dependent(fragment).scope) for (const b of level) b.bound = null;
  }), "a written scope", /a written application: the type argument for B's "T" .*does not establish its declared bound/);
  const relaxed = forgeDocument("invalid-computed-bound-typeof", "forged-written-bound", (fragment) => {
    const entries = fragment.declarations.applications.filter((a) => a.reference.name === "BoxOf");
    assert(entries.length > 0, "BoxOf<number>");
    for (const entry of entries) entry.bounds = entry.bounds.map(() => null);
  });
  // The bounds a written application is checked at are the document's
  // (the front end supplies every one): nulled, the application is
  // accepted.
  acceptedFile(relaxed, "the written bounds nulled");
  for (const [name, argument] of [["number", { k: "atom", name: "number", span }],
      ["callable", { k: "callable", span }]] as const)
    refusedFile(forgeDocument("blocker-returntype-typeof", `forged-returntype-${name}`, (fragment) => {
      must(fragment.declarations.applications.find((a) => a.reference.name === "ReturnType"), "ReturnType<typeof find>").args = [argument];
    }), `ReturnType at ${name}`, /the type argument for ReturnType's "T" .*does not establish its declared bound/);
  for (const [alias, argument] of [["Parameters", { k: "atom", name: "class", span }],
      ["ConstructorParameters", { k: "atom", name: "function", span }]] as const)
    refusedFile(forgeDocument("parameters-typeof", `forged-${alias}`, (fragment) => {
      must(fragment.declarations.applications.find((a) => a.reference.name === alias), alias).args = [argument];
    }), alias, new RegExp(`the type argument for ${alias}'s "T" .*does not establish its declared bound`));
  refusedFile(forgeDocument("written-dependent-default", "forged-short-reference", (fragment) => {
    let found = 0;
    visitAll(fragment.functions, (value) => {
      if (value.k === "reference" && Array.isArray(value.args) && (JSON.stringify(value.reference) ?? "").includes('"name":"Keys"')) {
        value.args.pop();
        found++;
      }
    });
    assert.ok(found, "a reference to Keys");
  }), "a short reference", /Keys applied to 1 type arguments of 2/);
  using exhausted = checkSource(join(root, "pipeline/examples/written-recursive-bound.ts"), undefined, false, 0, true);
  // Refused at the application, exhausted; the route reports the front's
  // refusal as unsupported.
  assert.ok(exhausted.status !== "verified" && exhausted.status !== "error", JSON.stringify(exhausted));
  assert.match("detail" in exhausted ? exhausted.detail : "", /source direct obligation at \[202,212\): subtype search exhausted/);
  say("binder roles, an unguarded alias, written arguments, scopes and references forged: each refused; a written obligation out of rounds exhausted");
});

control("forged declarations: the Promise tag", async (): Promise<void> => {
  // `Symbol.toStringTag` is the native `Promise` contract's: the declaration
  // document lists it by its identity, only that contract's prototype holds
  // it, its `then` names no `PromiseLike`, and no object the source makes is
  // keyed by it. A document tampered with in any of these is refused by the
  // pass.
  const tagged = (good: string, name: string, edit: (ast: Ast) => string, refusal: RegExp): void => {
    const path = join(good, `${name}.fragment.json`);
    writeFileSync(path, edit(readFragmentFile(fragmentOf(good))));
    refusedFile(pass(path), name, refusal);
  };
  const wellKnown = '"module":"typescript/lib/lib.es2015.symbol.wellknown.d.ts","name":"toStringTag"';
  const promises = run("async-await");
  const native = (ast: Ast) => must(ast.declarations.definitions.find(d =>
    d.declaration.name === "Promise" && d.declaration.module.startsWith("typescript/lib/")), "the native Promise");
  const untagged = /the native Promise contract states no readonly `Symbol.toStringTag` of type string/;
  tagged(promises, "tag-renamed", ast => {
    const text = JSON.stringify(ast);
    assert.ok(text.includes(wellKnown), "the tag's listed identity");
    return text.replace(wellKnown, wellKnown.replace('"toStringTag"', '"toStringTagX"'));
  }, untagged);
  tagged(promises, "tag-dropped", ast => {
    const index = ast.declarations.symbols.findIndex(s => JSON.stringify(s).includes(wellKnown));
    const text = JSON.stringify(native(ast));
    assert.ok(index >= 0 && text.includes(`"name":{"symbol":${index}}`), "the native prototype's tag");
    return JSON.stringify(ast).replace(text, text.replaceAll(`"name":{"symbol":${index}}`, '"name":"tag"'));
  }, untagged);
  tagged(promises, "tag-promise-like", ast => {
    const text = JSON.stringify(native(ast));
    const reference = '"reference":{"name":"Promise","span"';
    assert.ok(text.includes(reference), "a Promise the native then's callbacks return");
    return JSON.stringify(ast).replace(text, text.replace(reference, '"reference":{"name":"PromiseLike","span"'));
  }, /the native Promise contract names PromiseLike/);
  const fields = run("then-member-fields");
  tagged(fields, "tag-allocation", ast => {
    const index = ast.declarations.symbols.length;
    ast.declarations.symbols.push({ module: "typescript/lib/lib.es2015.symbol.wellknown.d.ts", name: "toStringTag",
      span: [0, 0] });
    const text = JSON.stringify(ast);
    assert.ok(text.includes('{"name":"then","e":'), "an allocation's then field");
    return text.replace('{"name":"then","e":', `{"name":{"symbol":${index}},"e":`);
  }, /an object the source makes is keyed by `Symbol.toStringTag`/);
  // `Fake` given the native contract's members at `number`, its methods
  // compatible with the native ones. As an exact copy its prototype is the
  // native record, and it verifies. With the tag dropped from its prototype,
  // its value returned as a `Promise<number>` is refused at the return:
  // dropping the tag makes the prototype a record of its own. With the tag
  // on a prototype of one more field, on Fake or on a base, or on a
  // prototype that is a callable object, the document is refused.
  const inherited = run("tag-fake-holder");
  // The copied contract with its prototype a callable object: every
  // prototype field writable, and a call signature.
  const callablePrototype = (text: string): string => {
    const contract: unknown = JSON.parse(text);
    const prototype = contract && typeof contract === "object" && "prototype" in contract ? contract.prototype : null;
    assert.ok(prototype && typeof prototype === "object" && "fields" in prototype && Array.isArray(prototype.fields) &&
      "calls" in prototype, "the copied prototype record");
    const fields: unknown[] = prototype.fields;
    for (const field of fields) if (field && typeof field === "object" && "readonly" in field) field.readonly = false;
    prototype.calls = [{ k: "function", effect: ordinaryEffect,
      receiver: null, params: [], rest: null,
      result: { k: "atom", name: "unknown", span: [0, 0] }, span: [0, 0] }];
    return must(JSON.stringify(contract), "the callable contract's text");
  };
  type FakeMode = "exact" | "untagged" | "distinct" | "base" | "callable";
  const fakeAt = (ast: Ast, mode: FakeMode): string => {
    const promise = native(ast);
    const fake = must(ast.declarations.definitions.find(d => d.declaration.name === "Fake"), "Fake");
    const index = ast.declarations.symbols.findIndex(s => JSON.stringify(s).includes(wellKnown));
    const text = JSON.stringify(must(promise.expression, "the native contract"))
      .replace(/\{"k":"parameter","index":0,"span":\[\d+,\d+\]\}/g, '{"k":"atom","name":"number","span":[0,0]}');
    const opening = '"prototype":{"k":"object","fields":[';
    assert.ok(text.includes(opening), "the copied prototype");
    const extra = '{"name":"forged","optional":false,"readonly":true,"type":{"k":"atom","name":"unknown","span":[0,0]},"span":[0,0]},';
    const body = mode === "exact" ? text
      : mode === "untagged" ? text.replace(new RegExp(`\\{"name":\\{"symbol":${index}\\}[^}]*\\}[^}]*\\},`), "")
      : mode === "callable" ? callablePrototype(text)
        : text.replace(opening, opening + extra);
    assert.ok(mode === "exact" || body !== text, `the ${mode} copy`);
    const replaced = mode === "base"
      ? JSON.stringify({ ...fake, bases: [JSON.parse(body)] })
      : JSON.stringify({ ...fake, bases: [], expression: JSON.parse(body) });
    return JSON.stringify(ast).replace(JSON.stringify(fake), replaced);
  };
  const at = readFileSync(sourceKey(inherited), "utf8").indexOf("return f;") + "return ".length;
  {
    const exact = join(inherited, "tag-fake-exact.fragment.json");
    writeFileSync(exact, fakeAt(readFragmentFile(fragmentOf(inherited)), "exact"));
    const produced = pass(exact);
    assert.ok(produced.status === 0 && [...produced.verdicts.values()].every((v) => v.closed), words(produced).slice(0, 1500));
  }
  // Refused at the read of `f` in `return f`, the refusal naming the node.
  tagged(inherited, "tag-fake-untagged", ast => fakeAt(ast, "untagged"), /expression at node \d+: Verification\.Tm\.var 0 /);
  assert.ok(at > 0);
  const otherPrototype = /a prototype holding `Symbol.toStringTag` other than the native Promise's/;
  tagged(inherited, "tag-fake-tagged", ast => fakeAt(ast, "distinct"), otherPrototype);
  tagged(inherited, "tag-fake-base", ast => fakeAt(ast, "base"), otherPrototype);
  tagged(inherited, "tag-fake-callable", ast => fakeAt(ast, "callable"), /a prototype is stated as no record/);
  say("forged tag documents: the tag renamed, dropped, stated of another prototype or a base's, PromiseLike in the native then, an allocation keyed by the tag; a contract with the native methods and no tag, a callable prototype: refused");
});

control("forged fragment: a reserved member name", async (): Promise<void> => {
  // The parser reserves `message` and `stack` as member names of a class
  // extending `Error`; the pass reads no class declaration: the fragment with
  // `text` renamed `stack` is accepted, the reservation the parser's alone.
  const methods = run("error-subclass-methods");
  const path = join(methods, "forged-stack-member-fragment.json");
  writeFileSync(path, readFileSync(fragmentOf(methods), "utf8").replaceAll('"text"', '"stack"').replaceAll("Located.text", "Located.stack"));
  assert.ok(readFileSync(path, "utf8").includes('"name":"stack"'), "the forged fragment names a member `stack`");
  const p = pass(path);
  assert.ok(p.status === 0 && [...p.verdicts.values()].every((v) => v.closed), words(p).slice(0, 1500));
  say("forged stack member: accepted by the pass, the reservation enforced by the parser alone");
});

control("forged fragment: writes renamed to a reserved key", async (): Promise<void> => {
  const twin = run("reserved-write-twin");
  const source = readFileSync(sourceKey(twin), "utf8");
  for (const [key, write] of [["stackPattern", "o.stackPattern"], ["stackUpdate", 'o.stackUpdate += "s"'],
      ["stackLogical", 'o.stackLogical ??= "s"'], ["stackCallback", "o.stackCallback = v"], ["stackComputed", 'o[k] = "s"']] as const) {
    const path = join(twin, `forged-${key}-fragment.json`);
    writeFileSync(path, readFileSync(fragmentOf(twin), "utf8").replaceAll(`"${key}"`, '"stack"'));
    const start = source.indexOf(write);
    const at = `source refusal at [${start},${start + write.length}): a write at a key that may be \`message\`, \`stack\` or \`cause\``;
    const p = pass(path);
    refusedFile(p, key);
    assert.ok(words(p).includes(at), `${key}: refused otherwise: ${words(p).slice(0, 1500)}`);
  }
  say("forged reserved writes: each write form renamed to `stack`, refused at the write");
});

control("forged declarations: a generic member's result", async (): Promise<void> => {
  // The class's declaration tampered to promise a number where the closure
  // returns its binder is refused at the construct code; the untampered one
  // is accepted. `make` alone is kept.
  const classGeneric = run("class-generic-method");
  const source = readFileSync(sourceKey(classGeneric), "utf8");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(classGeneric), "utf8"));
  assert.ok(isObject(fragment) && Array.isArray(fragment.functions));
  fragment.functions = fragment.functions.filter((f: unknown) => isObject(f) && f.name === "make");
  const kept = JSON.stringify(fragment);
  const at = source.indexOf("pick<V>(a: V): V") + "pick<V>(a: V): ".length;
  const declared = `"result":{"k":"binder","name":"V","span":[${at},${at + 1}]}`;
  assert.ok(kept.includes(declared), "pick's declared result");
  const search = (name: string, text: string): Pass => {
    const path = join(classGeneric, `${name}.json`);
    writeFileSync(path, text);
    return pass(path);
  };
  const derived = search("make-only", kept);
  assert.ok(derived.status === 0 && [...derived.verdicts.values()].every((v) => v.closed), words(derived).slice(0, 1500));
  const make = [...derived.verdicts.keys()].find((u) => u.startsWith("make@"));
  refused(search("forged-member-result", kept.replace(declared, '"result":{"k":"atom","name":"number","span":[0,0]}')),
    must(make, "make's unit"), "forged member result");
  say("forged declarations: a generic member's result narrowed in the class's declaration, refused at the construct code");
});

control("forged declarations: a typed array's view", async (): Promise<void> => {
  // A typed array's type is a view clause, its format stated by the
  // declaration's `view` and its members methods alone; the value is a
  // descriptor and its view spine. A record of the source given a `view`
  // (a user record shaped like a typed array) refuses the unit reading it;
  // the untampered document is accepted.
  const artifacts = run("typed-array-length-across-field-write");
  const text = readFileSync(fragmentOf(artifacts), "utf8");
  const document = (t: string): Record<string, unknown> => {
    const value: unknown = JSON.parse(t);
    assert.ok(isObject(value), "a fragment");
    return value;
  };
  const good = pass(forged(artifacts, "views-kept", document(text)));
  const marked = must([...good.verdicts.keys()].find((u) => u.startsWith("marked@")), "marked's unit");
  accepted(good, marked, "the untampered views");
  const cursor = /("name":"Cursor","span":\[\d+,\d+\]\},"parameters":\[\],"bases":\[\],"expression":\{"k":"object",)/;
  assert.ok(cursor.test(text), "Cursor's definition");
  const shaped = pass(forged(artifacts, "forged-record-view", document(text.replace(cursor, '$1"view":"uint8",'))));
  refused(shaped, marked, "a record of the source given a view",
    /the declarations required by this unit cannot be interpreted: Cursor: a typed array's type states its methods alone/);
  // A typed array's declaration given an array-spine slot `[]`: a typed
  // array has one spine, its descriptor's, so the declaration is refused.
  const uint8 = /("name":"Uint8Array","span":\[0,0\]\},"parameters":\[\],"bases":\[\],"expression":\{"k":"object","fields":\[)/;
  assert.ok(uint8.test(text), "Uint8Array's definition");
  const slot = '{"name":"[]","optional":false,"readonly":false,"type":{"k":"atom","name":"number","span":[0,0]},"span":[0,0]},';
  const stored = pass(forged(artifacts, "forged-view-spine-slot", document(text.replace(uint8, `$1${slot}`))));
  refused(stored, marked, "a typed array given an array-spine slot",
    /Uint8Array: a declared member cannot use the model's internal key/);
  say("forged declarations: a record of the source given a view, and a typed array given `[]`, refused at their declarations");
});

control("forged declarations: another import closure", async (): Promise<void> => {
  // A fragment's code over another file's declarations. The code names each
  // declaration it reads by its identity (module, name, span): a reference
  // whose identity the other closure has no definition of refuses the unit
  // reading it at the annotation; a unit reading no declaration (values'
  // `identity`) is checked as before, its verdict independent of them.
  const reading = run("collections-json-uninherited-key");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(reading), "utf8"));
  const other: unknown = JSON.parse(readFileSync(fragmentOf(run("values")), "utf8"));
  assert.ok(isObject(fragment) && isObject(other) && "declarations" in other);
  const swapped = pass(forged(reading, "forged-import", { ...fragment, declarations: other.declarations }));
  for (const unit of ["nest@197", "lookup@262"])
    refused(swapped, unit, "a unit reading a declaration over another closure",
      /source refusal at \[\d+,\d+\): the declarations required by this unit cannot be interpreted: reference has no declaration equation/);
  const good = run("values");
  const own: unknown = JSON.parse(readFileSync(fragmentOf(good), "utf8"));
  assert.ok(isObject(own) && isObject(fragment) && "declarations" in fragment);
  const kept = pass(forged(good, "forged-import", { ...own, declarations: fragment.declarations }));
  accepted(kept, "identity@9", "a unit reading no declaration");
  say("forged import closure: a unit reading a declaration the other closure has no definition of refused at its annotation; one reading none checked as before");
});

control("forged declarations: unequal bound member effects", async (): Promise<void> => {
  // A method bound to a union of hosts needs each host's member at one
  // signature: one host's `next` given the empty effect.
  const artifacts = run("bind-union-host");
  const ast = fragmentAst(artifacts);
  honest("bind-union-host", "total@1704");
  const host = must(ast.declarations.definitions.find((d) => d.declaration.name === "Countdown"), "Countdown");
  assert.ok(host.expression?.k === "object");
  const next = must(host.expression.fields.find((f) => f.name === "next"), "Countdown.next");
  const forms = next.type.k === "intersection" ? next.type.parts : [next.type];
  assert.ok(forms.length > 0);
  for (const form of forms) {
    assert.ok(form.k === "function");
    assert.deepEqual(form.effect, ordinaryEffect);
    form.effect = emptyEffect;
  }
  refused(pass(forged(artifacts, "unequal-bound-member-effects", ast)), "total@1704", "unequal member effects");
  say("unequal bound member effects: refused at the bound call's unit");
});

control("forged fragment: explicit type arguments widened", async (): Promise<void> => {
  // `reduce<number | null>` written as `reduce<number | null | string>`, and
  // `same<number | boolean>` as `same<number | boolean | string>`.
  for (const [file, kind] of [["closure-result-contract", "invoke"], ["explicit-type-arguments", "apply"]] as const) {
    const artifacts = run(file);
    const unforced = pass(fragmentOf(artifacts));
    const ast: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
    const calls: { parts: unknown[]; span: unknown }[][] = [];
    const found: { owner: string | null } = { owner: null };
    visitAll(ast, (node) => {
      if (node.k === kind && Array.isArray(node.typeArgs) && node.typeArgs.length > 0 && calls.length === 0)
        calls.push(node.typeArgs.filter((a): a is { parts: unknown[]; span: unknown } => isObject(a) && Array.isArray(a.parts)));
      if (calls.length > 0 && found.owner === null && typeof node.name === "string" && Array.isArray(node.namePos) &&
          typeof node.namePos[0] === "number" && "body" in node) found.owner = `${node.name}@${node.namePos[0]}`;
    });
    const [typeArg] = must(calls[0], "the call's type arguments");
    must(typeArg, "the type argument").parts.push({ k: "atom", name: "string", span: typeArg?.span });
    assert.ok(isObject(ast));
    const unit = must(found.owner, "the call's function");
    honest(file, unit, unforced);
    refused(pass(forged(artifacts, "forged-type-argument", ast)), unit, `${file} widened`);
  }
  say("explicit type arguments written wider than the call's instance: refused at the call's unit");
});

control("forged fragment: an array owning toJSON", async (): Promise<void> => {
  const artifacts = run("json-stringify-sparse");
  const ast = fragmentAst(artifacts);
  const nested = must(ast.functions.find((f) => f.name === "nested"), "nested's declaration");
  const unit = unitOf(ast, "nested");
  honest("json-stringify-sparse", unit);
  const rows = must(nested.params[0], "nested's parameter");
  const span = rows.type.span;
  rows.type = { k: "intersection", span, parts: [rows.type, { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "toJSON", optional: false, readonly: false, span, type: { k: "function", effect: ordinaryEffect,
      receiver: null, params: [], rest: null, result: { k: "atom", name: "undefined", span }, span } }] }] };
  refused(pass(forged(artifacts, "forged-array-tojson", ast)), unit, "forged", /intersection is empty/);
  say("an array owning toJSON, forged past the parser: refused at the empty intersection");
});

/** A statement keeping every location, on a throw too: `Modifies<{}, T>`. */
const emptyStatement: StatedFrame = { footprint: { value: "keep", spine: "keep" }, onThrow: false, fresh: false, regions: [] };

control("forged fragment: a generic closure's statement", async (): Promise<void> => {
  const artifacts = run("generic-function-type-annotation");
  const fragment = readFileSync(fragmentOf(artifacts), "utf8");
  const lambda = fragment.search(/"k":"lambda","pos":\[\d+,\d+\],"typeParams":\[\{/);
  assert.ok(lambda >= 0, "a generic closure");
  const unstated = fragment.indexOf('"stated":null', lambda);
  assert.ok(unstated > lambda, "its statement");
  const path = join(artifacts, "forged-generic-stated-fragment.json");
  writeFileSync(path, fragment.slice(0, unstated) +
    `"stated":${JSON.stringify(statedExits(emptyStatement))}` + fragment.slice(unstated + '"stated":null'.length));
  refusedFile(pass(path), "forged", /a generic closure states no effect/);
  say("stated generic closure: a statement written into the Fragment refused");
});

control("forged fragment: a method's statement dropped", async (): Promise<void> => {
  // The class's construction is checked against the member's statement:
  // with `bump`'s statement dropped, the class is still refused.
  const artifacts = run("invalid-method-effect-construction");
  const fragment = readFileSync(fragmentOf(artifacts), "utf8");
  const statement = `"stated":${JSON.stringify(statedExits(emptyStatement))}`;
  assert.equal(fragment.split(statement).length, 2, "bump's statement");
  const path = join(artifacts, "forged-unstated-fragment.json");
  writeFileSync(path, fragment.replace(statement, '"stated":null'));
  const unforced = pass(fragmentOf(artifacts));
  const p = pass(path);
  refusedFile(p, "forged");
  // Refused where the honest document is: the construction.
  for (const [u, v] of unforced.verdicts) if (!v.closed) refused(p, u, `forged: ${u}`);
  say("unstated method of a stated member: the class's construction refused, the Fragment's statement dropped");
});

control("stated import: the exporting module refused", async (): Promise<void> => {
  // An import with a body is read at what its declaration states only where
  // its module's check establishes it; `drain`'s statement is refused there,
  // so the importer reads it at the ordinary effect and is refused.
  using importer = checkSource(join(root, "pipeline/examples/invalid-stated-assumed-value-import.ts"),
    tsconfigOf(join(root, "pipeline/imports-project")), false, undefined, true);
  const project = join(root, "pipeline/imports-project");
  using outcome = checkSource(join(project, "stated.ts"), tsconfigOf(project), false, undefined, true);
  assert.notEqual(importer.status, "verified", JSON.stringify(importer).slice(0, 1500));
  if (outcome.status === "verified") assert.fail("drain's module verified");
  const drain = must((outcome.units ?? []).find((u) => u.unit.startsWith("drain@")), "drain's unit");
  assert.notEqual(drain.status, "verified");
  assert.match(drain.detail, /footprint/);
  say("stated import: the exporting module's drain refused at its footprint, the importer refused at the ordinary effect");
});

control("exhausted footprint check", async (): Promise<void> => {
  // A check that runs out of subtype rounds is inconclusive, not a refusal.
  using searched = checkSource(join(root, "pipeline/examples/declaration-preserving-callback.ts"), undefined, false, 1, true);
  assert.equal(searched.status, "exhausted", JSON.stringify(searched).slice(0, 1500));
  assert.match("detail" in searched ? searched.detail : "", /exhausted/);
  assert.doesNotMatch("detail" in searched ? searched.detail : "", /source effect refusal/);
  say(`exhausted footprint check: reported exhausted (${searched.status})`);
});

/** The unit of the function whose code holds the source offset `at`: the
 * last function of the fragment whose name precedes it. */
function unitHolding(ast: Ast, at: number): string {
  const before = ast.functions.filter((f) => f.namePos[0] <= at).sort((a, b) => b.namePos[0] - a.namePos[0]);
  const fn = must(before[0], `a function before ${at}`);
  return `${fn.name}@${fn.namePos[0]}`;
}

control("forged fragment: a guard's promise removed", async (): Promise<void> => {
  // A call narrows its argument by the promise the document states of its
  // callee: with the promise removed from `isPresence`, its caller is refused.
  const artifacts = run("type-guards");
  const ast = fragmentAst(artifacts);
  const isPresence = must(ast.functions.find((f) => f.name === "isPresence"), "isPresence");
  assert.ok(isPresence.guard, "isPresence states a promise");
  const caller = unitHolding(ast, readFileSync(sourceKey(artifacts), "utf8").indexOf("isPresence(v)"));
  honest("type-guards", caller);
  isPresence.guard = null;
  refused(pass(forged(artifacts, "forged-unpromised-guard", ast)), caller, "unpromised");
  say(`unpromised guard call: its caller ${caller} refused`);
});

control("forged fragment: a regex shape no declaration lists", async (): Promise<void> => {
  const artifacts = run("regexp-structural");
  const text = readFileSync(fragmentOf(artifacts), "utf8");
  const call = /"callee":\{"k":"id","pos":\[\d+,\d+\],"name":"%RegExp:1%"\}/.exec(text)?.[0];
  assert.ok(call, "a literal's call names its shape");
  const path = join(artifacts, "forged-regexp-shape.json");
  writeFileSync(path, text.replace(call, call.replace("%RegExp:1%", "%RegExp:111%")));
  refusedFile(pass(path), "forged", /%RegExp:111%/);
  say("forged regex shape: a literal naming a shape no declaration lists refused");
});

control("host reading on a stand-in host", async (): Promise<void> => {
  // Reading rule 1 on a stand-in host package (`pipeline/host-fixture/`,
  // whose `Node` reaches no node list), activated by the compiler API's
  // description naming the stand-in's installation and digest: the shape
  // omits the allocating `jsDoc`, so every form of its read is refused, and
  // reads of other members verify. The stand-in declares no `tokenCache`, so
  // the description omits `jsDoc` alone.
  const project = tsconfigOf(join(root, "pipeline/host-fixture-project"));
  const example = (file: string): string => join(root, "pipeline/examples", `${file}.ts`);
  useFamiliesForTests([{ ...compilerApiFamily, installation: { from: "pipeline/host-fixture-project",
    digest: "1f729218dade5923e3787adb29cda54fc8b923d88f0b35892b11fa70d5ec42fe" },
    omitted: compilerApiFamily.omitted.filter(m => m.member === "jsDoc") }]);
  const jsDocRead = /source expression obligation at \[\d+,\d+\): refused at a read: read of a field 'jsDoc' the contract does not name/;
  try {
    for (const [form, refusal] of [
      // The route's refusal of the read, at its span; a template key and a
      // binding are refused as forms the pass does not handle (undetermined
      // types), the view at its node.
      ["dot", jsDocRead], ["element", jsDocRead], ["paren-key", jsDocRead], ["const-key", jsDocRead],
      ["template-key", /source expression obligation at \[\d+,\d+\): not handled: an element read of a value that is no array/],
      ["binding", /source expression obligation at \[\d+,\d+\): not handled: the bound value undetermined/], ["optional", jsDocRead],
      ["view", /expression at node \d+: Verification\.Tm\.var 0 /],
    ] as const) {
      using outcome = checkSource(example(`invalid-host-fixture-jsdoc-${form}`), project, false, undefined, true);
      assert.notEqual(outcome.status, "verified", `invalid-host-fixture-jsdoc-${form}: refused`);
      assert.ok("detail" in outcome && refusal.test(outcome.detail), `invalid-host-fixture-jsdoc-${form}: ${JSON.stringify(outcome)}`);
    }
    // Node lists: read as dense readonly arrays owning their stated members, each readonly.
    using rows = checkSource(example("host-fixture-node-list"), project, false, undefined, true);
    assert.equal(rows.status, "verified", JSON.stringify(rows));
    using written = checkSource(example("invalid-host-fixture-node-list-write"), project, false, undefined, true);
    assert.ok(written.status !== "verified" && "detail" in written && /transformFlags/.test(written.detail),
      JSON.stringify(written));
    // Branded strings (reading rule 5): read as strings, refused as a host
    // parameter (L5).
    using branded = checkSource(example("host-fixture-branded-read"), project, false, undefined, true);
    assert.equal(branded.status, "verified", JSON.stringify(branded));
    for (const [file, refusal] of [
      ["invalid-host-fixture-branded-parameter", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-callback-result", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-held", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-argument", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-nested", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-curried", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-optional-parameter", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-return", /the intersection is empty/],
      ["invalid-host-fixture-branded-alias", /the intersection is empty/],
    ] as const) {
      using refused = checkSource(example(file), project, false, undefined, true);
      assert.ok(refused.status !== "verified" && "detail" in refused && refusal.test(refused.detail),
        `${file}: ${JSON.stringify(refused)}`);
    }
    for (const file of ["host-fixture-branded-callback", "host-fixture-branded-positions"]) {
      using supplied = checkSource(example(file), project, false, undefined, true);
      assert.equal(supplied.status, "verified", `${file}: ${JSON.stringify(supplied)}`);
    }
    // A member declared `any`: optional, of type `unknown` (reading rule 2).
    using brand = checkSource(example("host-fixture-brand-optional"), project, false, undefined, true);
    assert.equal(brand.status, "verified", JSON.stringify(brand));
    using required = checkSource(example("invalid-host-fixture-brand-required"), project, false, undefined, true);
    assert.ok(required.status === "unverified" && /expression at node \d+: Verification\.Tm\.invoke/.test(required.detail),
      JSON.stringify(required));
    using kept = checkSource(example("host-fixture-jsdoc-other-reads"), project, false, undefined, true);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    using lookalike = checkSource(example("host-fixture-lookalike"), project, false, undefined, true);
    // Refused at the read of jsDoc.
    assert.ok(lookalike.status !== "verified" && "detail" in lookalike && jsDocRead.test(lookalike.detail), JSON.stringify(lookalike));
  } finally {
    useFamiliesForTests(null);
  }
  say("host reading on a stand-in host: every read of jsDoc refused; other reads verified; a node list read as a dense readonly array, a write to its member refused; a branded string read as a string where the host produces it, refused where the client would; a member declared any optional");
});


control("forged fragment: guard domains", async (): Promise<void> => {
  // A family guard's call stated at a domain its argument is not within
  // (`never`), with the entry's tags and with none, refused at the call; one
  // stating no domain refused by the decoder.
  const calls: [string, string][] = [
    ["compiler-api-guard-false-branch", "ts.isIdentifier(node)"],
    ["compiler-api-guard-values", "ts.isIdentifier(n)"],
    ["compiler-api-guards", "isStringLiteral(node)"],
  ];
  for (const [file, text] of calls) {
    const artifacts = run(file);
    const start = readFileSync(sourceKey(artifacts), "utf8").indexOf(text);
    const document: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
    assert.ok(isObject(document));
    const found: Record<string, unknown>[] = [];
    visitAll(document, (v) => {
      if (v.k === "tagMember" && Array.isArray(v.pos) && v.pos[0] === start) found.push(v);
    });
    const [call] = found;
    assert.ok(call && found.length === 1 && Array.isArray(call.pos), `${file}: the guard's call ${text}`);
    const caller = unitHolding(fragmentAst(artifacts), start);
    honest(file, caller);
    const { domain, tags } = call;
    const forgedDocument = (name: string, replaced: unknown, replacedTags: unknown): Pass => {
      call.domain = replaced;
      call.tags = replacedTags;
      const p = pass(forged(artifacts, `${name}.fragment`, document));
      call.domain = domain;
      call.tags = tags;
      return p;
    };
    const never = { k: "atom", name: "never", span: call.pos };
    const variants: { variant: string; replacedTags: unknown }[] = [{ variant: "entry", replacedTags: tags },
      { variant: "empty", replacedTags: [] }];
    for (const { variant, replacedTags } of variants)
      refused(forgedDocument(`forged-guard-domain-${variant}`, never, replacedTags), caller, `${file}, ${variant} tags`);
    refusedFile(forgedDocument("forged-guard-no-domain", null, tags), `${file}: no domain`, /a family guard's call states its guard's domain/);
  }
  say("forged guard domains: a domain the argument is not within, with the entry's tags and with none, in a condition, a callback's body and a negated condition, refused at the call's unit; a call without its domain by the decoder");
});

for (const copy of [false, true]) control(`nested installations: ${copy ? "a copy" : "a link"}`, async (): Promise<void> => {
  const installation = resolve(root, "tools", "node_modules", "typescript");
  const dir = runDirectory(`tscert-nested-${copy ? "copied" : "linked"}-`);
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
    module: "preserve", moduleResolution: "bundler", target: "es2022", verbatimModuleSyntax: true, types: [],
    paths: { "typescript/unstable/ast": [join(installation, "dist", "ast", "index.d.ts")] } }, include: ["*.ts"] }));
  const source = join(dir, "name.ts");
  writeFileSync(source, 'import * as ts from "typescript/unstable/ast";\n\n' +
    "export function name(n: ts.Node): string {\n  return ts.isIdentifier(n) ? n.text : \"\";\n}\n");
  mkdirSync(join(dir, "node_modules"));
  const target = join(dir, "node_modules", "typescript");
  if (copy) cpSync(installation, target, { recursive: true, dereference: true });
  else symlinkSync(installation, target);
  using outcome = checkSource(source, tsconfigOf(dir), false, undefined, true);
  if (!copy) assert.equal(outcome.status, "verified", JSON.stringify(outcome));
  else assert.ok(outcome.status !== "verified" && /missing field text|read of a field 'text' the contract does not name/.test(outcome.detail), JSON.stringify(outcome));
  say(copy ? "nested installations: a copy of the audited package in the client's node_modules is no guard"
    : "nested installations: the audited package linked narrows");
});

/** The pipeline directory. */
const here = join(root, "pipeline");
/** A source checked on the route, its artifacts retained. */
function check(source: string, project?: string, typescriptErrors: boolean = false, subtypeRounds?: number): Outcome {
  return checkSource(source, project, typescriptErrors, subtypeRounds, true);
}

control("declared-optional method on a stand-in family", async (): Promise<void> => {
  // A method declared optional (HOST-FAMILIES.md, "The family contract"):
  // on a stand-in host package whose family root declares `describe?()`
  // beside `text()`, each shape names the shared definition of `text` as a
  // base and states `describe` as its own optional member, and its call is
  // refused at the call.
  const project = tsconfigOf(join(here, "family-fixture-project"));
  const example = (file: string): string => join(here, "examples", `${file}.ts`);
  useFamiliesForTests([{ ...compilerApiFamily, installation: { from: "pipeline/family-fixture-project",
    digest: "aaaa66cf18b7f7d980c0e7734ae6421159ac2eccbbaa8d28b76f03e4280701ff" },
  table: [{ rule: "literal" }], corrections: [], omitted: [], footprints: [] }]);
  try {
    const kept = check(example("family-fixture-optional-method"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    const first = must(must(readFragmentFile(join(kept.artifacts, "fragment.json")).declarations, "the declarations")
      .definitions.find((d) => d.declaration.name === "First"), "First's reading");
    assert.deepEqual(first.bases.map((b) => b.k === "reference" ? b.reference.name : b.k), ["Node.text"]);
    assert.ok(first.expression?.k === "object" && first.expression.fields.some((f) => f.name === "describe" && f.optional),
      "First states describe optional");
    const file = example("invalid-family-fixture-optional-method");
    const refused = check(file, project);
    const at = readFileSync(file, "utf8").indexOf("n.describe");
    assert.ok(refused.status !== "verified" && refused.detail.includes(`at [${at},`) /* refused at a span starting at the call */, JSON.stringify(refused));
  } finally {
    useFamiliesForTests(null);
  }
  process.stdout.write("declared-optional method: each shape's own optional member, the required one shared, its call refused\n");
});
control("a compiler-API method a correction makes absent", async (): Promise<void> => {
  // A correction of a method to absent (HOST-FAMILIES.md, "The family
  // contract"): under a description correcting `getText` at one tag, the
  // method is an optional member of every reading covering that tag (the
  // tag's own shape, a generic declaration applied at any of its tags, a
  // selected generic arm, a residual holding the tag), so each call is
  // refused at its read; under the compiler API's own description each
  // verifies. The route reads only the document of the description it runs
  // under.
  const project = tsconfigOf(join(here, "compiler-api-project"));
  const getText = (kind: string) => ({ kind, owner: "Node", member: "getText", text: "getText(sourceFile?: SourceFile): string;" });
  const corrected = [
    ["SourceFile", "compiler-api-corrected-method", "f.getText"],
    ["SourceFile", "compiler-api-corrected-residual", "n.getText"],
    ["QuestionToken", "compiler-api-corrected-token", "t.getText"],
    ["QuestionToken", "compiler-api-corrected-arm", "n.getText"],
    ["QuestionToken", "compiler-api-corrected-residual", "n.getText"],
  ] as const;
  const example = (file: string): string => join(here, "examples", `${file}.ts`);
  for (const name of new Set(corrected.map(([, file]) => file))) {
    const plain = check(example(name), project);
    assert.equal(plain.status, "verified", `${name}: ${JSON.stringify(plain)}`);
  }
  for (const [kind, name, read] of corrected) {
    useFamiliesForTests([{ ...compilerApiFamily, corrections: [...compilerApiFamily.corrections, getText(kind)] }]);
    try {
      const file = example(name);
      const outcome = check(file, project);
      const at = readFileSync(file, "utf8").indexOf(read);
      const located = outcome.status !== "verified" &&
        [...outcome.detail.matchAll(/at \[(\d+),(\d+)\)/g)].some((m) => Number(m[1]) <= at && at < Number(m[2]));
      assert.ok(located, `${name} with getText corrected at ${kind}: refused at ${read}: ${JSON.stringify(outcome)}`);
    } finally {
      useFamiliesForTests(null);
    }
  }
  process.stdout.write("corrected method: each call of a method a correction makes absent refused at its read, each verified uncorrected\n");
});

control("a string-tagged family", async (): Promise<void> => {
  // A second family (HOST-FAMILIES.md, "Instances"): a stand-in package of
  // string-tagged units, activated beside the compiler API's by a
  // description of its own, which names the stand-in's package, its
  // installation and its digest, its tag `type`, a string, and a guard table
  // that activates over the stand-in's own modules. A guard of one tag and
  // one through a helper of its tag narrow both edges, each call a
  // membership test of the family's string constants; a guard whose answer
  // depends on an option argument has no entry and narrows nothing.
  const project = tsconfigOf(join(here, "string-family-fixture-project"));
  const example = (file: string): string => join(here, "string-family-fixture-project", `${file}.ts`);
  const strings: FamilyDescription = stringFamily;
  // The stand-in's description beside the compiler API's: the active
  // descriptions, the whole of what the run is given.
  const activate = (description: FamilyDescription): void => useFamiliesForTests([compilerApiFamily, description]);
  activate(strings);
  try {
    const kept = check(example("guards"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    const tagSets: string[] = [];
    const visit = (v: unknown): void => {
      if (Array.isArray(v)) v.forEach(visit);
      else if (typeof v === "object" && v !== null) {
        if ("k" in v && v.k === "tagMember" && "tags" in v) tagSets.push(JSON.stringify(v.tags) ?? "");
        Object.values(v).forEach(visit);
      }
    };
    visit(JSON.parse(readFileSync(join(kept.artifacts, "fragment.json"), "utf8")));
    assert.ok(tagSets.includes(JSON.stringify([{ a: "stringlit", v: "call" }, { a: "stringlit", v: "name" }]) ?? ""),
      `isExpression's call tests the family's string constants: ${tagSets.join(" ")}`);
    const file = example("invalid-loose");
    const refused = check(file, project);
    const at = readFileSync(file, "utf8").lastIndexOf("n.name");
    // Refused at a span holding the read, reading `name`.
    const spans = [...("detail" in refused ? refused.detail : "").matchAll(/at \[(\d+),(\d+)\)/g)].map((m) => [Number(m[1]), Number(m[2])]);
    assert.ok(refused.status !== "verified" && spans.some(([a, b]) => a <= at && at < b) &&
      /read of a field 'name'|missing field name/.test(refused.detail), JSON.stringify(refused));
    // The tag enum read as a value, by the description alone: its members
    // are the runtime object the activated entry point exports. Over a copy
    // whose `kinds.js` gives `Literal` another value, its guard table
    // activated over the copy's own digests, the same program is refused at
    // the read, and under Node `literalTag` returns the runtime value, not
    // its declared `"literal"`.
    const kinds = check(example("kinds"), project);
    assert.equal(kinds.status, "verified", JSON.stringify(kinds));
    // The compiler API's named views apply to its installation alone: the
    // stand-in's `Program` and `API`, of the views' names, are read by their
    // own declarations.
    const views = check(example("views"), project);
    assert.equal(views.status, "verified", JSON.stringify(views));
    {
      const copy = runDirectory("tscert-tag-enum-");
      const installed = join(copy, "node_modules", "string-family-fixture");
      mkdirSync(join(copy, "node_modules"));
      cpSync(join(here, "string-family-fixture"), installed, { recursive: true });
      const runtime = readFileSync(join(installed, "kinds.js"), "utf8").replace('UnitType["Literal"] = "literal"', 'UnitType["Literal"] = "lit"');
      assert.ok(runtime.includes('"lit"'), "the copy's runtime enum differs");
      writeFileSync(join(installed, "kinds.js"), runtime);
      cpSync(join(here, "string-family-fixture-project", "tsconfig.json"), join(copy, "tsconfig.json"));
      cpSync(example("kinds"), join(copy, "kinds.ts"));
      activate({ ...strings, installation: { ...strings.installation, from: copy },
        guards: { ...strings.guards, closure: { ...strings.guards.closure, files: { ...strings.guards.closure.files,
          "kinds.js": createHash("sha256").update(runtime).digest("hex") } } } });
      const mismatched = check(join(copy, "kinds.ts"), tsconfigOf(copy));
      assert.ok(mismatched.status === "unsupported" && /the host enum UnitType is not one .* nor a family's tag enum its runtime object matches/.test(mismatched.detail),
        JSON.stringify(mismatched));
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { literalTag } from ${JSON.stringify(pathToFileURL(join(copy, "kinds.ts")).href)};\nconsole.log(literalTag());\n`],
        { encoding: "utf8", cwd: copy });
      assert.equal(ran.stdout.trim(), "lit", `literalTag under Node: ${ran.stderr}`);
      activate(strings);
    }
    {
      // The tag enum's binding is the object activation checked, as Node
      // resolves the client's import: a project whose `paths` point
      // TypeScript at the stand-in's audited declarations while Node loads a
      // copy whose `Literal` is "lit" is refused at the read; with Node
      // loading the audited installation, the same program verifies.
      const bindingRun = (name: string, target: string, change: ((dir: string) => void) | null): { outcome: Outcome; dir: string } => {
        const dir = runDirectory(`tscert-tag-binding-${name}-`);
        writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
          module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
          paths: { "string-family-fixture/ast": [join(here, "string-family-fixture", "ast.d.ts")] } }, include: ["*.ts"] }));
        mkdirSync(join(dir, "node_modules"));
        const installed = join(dir, "node_modules", "string-family-fixture");
        if (change) {
          cpSync(target, installed, { recursive: true });
          change(installed);
        } else symlinkSync(target, installed);
        cpSync(example("kinds"), join(dir, "kinds.ts"));
        return { outcome: check(join(dir, "kinds.ts"), tsconfigOf(dir)), dir };
      };
      const audited = bindingRun("audited", join(here, "string-family-fixture"), null);
      assert.equal(audited.outcome.status, "verified", JSON.stringify(audited.outcome));
      const other = bindingRun("other", join(here, "string-family-fixture"), (installed) => {
        const runtime = readFileSync(join(installed, "kinds.js"), "utf8").replace('UnitType["Literal"] = "literal"', 'UnitType["Literal"] = "lit"');
        writeFileSync(join(installed, "kinds.js"), runtime);
      });
      assert.ok(other.outcome.status === "unsupported" && /the host enum UnitType is not one .* nor a family's tag enum its runtime object matches/.test(other.outcome.detail),
        JSON.stringify(other.outcome));
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { literalTag } from ${JSON.stringify(pathToFileURL(join(other.dir, "kinds.ts")).href)};\nconsole.log(literalTag());\n`],
        { encoding: "utf8", cwd: other.dir });
      assert.equal(ran.stdout.trim(), "lit", `literalTag under Node, its import bound to the copy: ${ran.stderr}`);
    }
    {
      // Guard recognition stays within one family: a second family, a copy
      // of the stand-in under another name and marker whose `UnitType.Name`
      // is "nm", is active beside it, with guards and a domain of the same
      // names. A project whose `paths` point TypeScript at the stand-in's
      // declarations while Node binds `isName` to the copy's is no guard
      // call, refused at the return of the `false` edge's tag; with Node binding the
      // stand-in's, it verifies.
      const source = 'import { isName, type Unit } from "string-family-fixture/ast";\n\n' +
        'export function tagOf(n: Unit): "call" | "literal" | "" {\n  return isName(n) ? "" : n.type;\n}\n';
      const project = (name: string): string => {
        const dir = runDirectory(`tscert-guard-family-${name}-`);
        writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
          module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
          paths: { "string-family-fixture/ast": [join(here, "string-family-fixture", "ast.d.ts")] } }, include: ["*.ts"] }));
        writeFileSync(join(dir, "tag-of.ts"), source);
        mkdirSync(join(dir, "node_modules"));
        return dir;
      };
      const same = project("same");
      symlinkSync(join(here, "string-family-fixture"), join(same, "node_modules", "string-family-fixture"));
      const crossed = project("crossed");
      const copy = join(crossed, "node_modules", "string-family-fixture-b");
      cpSync(join(here, "string-family-fixture"), copy, { recursive: true });
      const manifest: unknown = JSON.parse(readFileSync(join(copy, "package.json"), "utf8"));
      assert.ok(typeof manifest === "object" && manifest !== null);
      writeFileSync(join(copy, "package.json"), JSON.stringify({ ...manifest, name: "string-family-fixture-b" }));
      const kinds = readFileSync(join(copy, "kinds.js"), "utf8").replace('UnitType["Name"] = "name"', 'UnitType["Name"] = "nm"');
      writeFileSync(join(copy, "kinds.js"), kinds);
      symlinkSync(copy, join(crossed, "node_modules", "string-family-fixture"));
      const second: FamilyDescription = { ...strings, package: { ...strings.package, name: "string-family-fixture-b" },
        installation: { ...strings.installation, from: crossed }, marker: "StringFixtureB",
        guards: { ...structuredClone(strings.guards), closure: { ...strings.guards.closure, files: { ...strings.guards.closure.files,
          "kinds.js": createHash("sha256").update(kinds).digest("hex") } } } };
      useFamiliesForTests([compilerApiFamily, strings, second]);
      try {
        const verified = check(join(same, "tag-of.ts"), tsconfigOf(same));
        assert.equal(verified.status, "verified", JSON.stringify(verified));
        const refused = check(join(crossed, "tag-of.ts"), tsconfigOf(crossed));
        const returned = source.indexOf("isName(n) ?");
        // Refused, at the return's span with the tag set it fails or at the
        // node (`expression at node N`).
        assert.ok(refused.status !== "verified" && "detail" in refused && (refused.detail.includes(`at [${returned},`) &&
          refused.detail.includes('"" | "call" | "literal" | "name"') ||
          /single pass: refused: expression at node \d+: Verification\.Tm\.var 0 /.test(refused.detail)), JSON.stringify(refused));
      } finally {
        activate(strings);
      }
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { tagOf } from ${JSON.stringify(pathToFileURL(join(crossed, "tag-of.ts")).href)};\nconsole.log(tagOf({ type: "name" }));\n`],
        { encoding: "utf8", cwd: crossed });
      assert.equal(ran.stdout.trim(), "name", `tagOf under Node, isName bound to the copy: ${ran.stderr}`);
    }
    // Activation fails closed: under a description whose digest differs from
    // the stand-in's declarations, or whose installation Node does not find,
    // the same program is refused; with no stand-in description its guards
    // narrow nothing.
    for (const [what, description, refusal] of [
      ["another digest", { ...strings, installation: { ...strings.installation, digest: "0".repeat(64) } },
        /is not the one the family StringFixture was reviewed against/],
      ["an installation Node does not find", { ...strings, installation: { ...strings.installation, from: "pipeline/host-fixture-project" } },
        /the family StringFixture's package string-family-fixture does not resolve from pipeline\/host-fixture-project/],
    ] as const) {
      activate(description);
      const closed = check(example("guards"), project);
      assert.ok(closed.status !== "verified" && "detail" in closed && refusal.test(closed.detail), `${what}: ${JSON.stringify(closed)}`);
    }
    useFamiliesForTests([compilerApiFamily]);
    const inactive = check(example("guards"), project);
    assert.ok(inactive.status !== "verified", `no stand-in description: ${JSON.stringify(inactive)}`);
    activate(strings);
    // Stable members through the same code (HOST-FAMILIES.md, "Stable
    // keys"): every property member of the stand-in is stable, so a callee
    // tested and read past a call is the tested value; the description
    // excluding `Call.callee`, the one thing changed, refuses the read.
    const stable = check(example("stable"), project);
    assert.equal(stable.status, "verified", JSON.stringify(stable));
    activate({ ...strings, stable: { excluded: [{ owner: "Call", member: "callee", text: "readonly callee: Unit;" }] } });
    const excluded = check(example("stable"), project);
    const read = readFileSync(example("stable"), "utf8").lastIndexOf("c.callee.name");
    assert.ok(excluded.status !== "verified" && excluded.detail.includes(`at [${read},`), JSON.stringify(excluded));
    // The tag's stability follows its declarations, a residual's too: with
    // `Literal.type` excluded, the residual standing for `Literal` states no
    // stable tag, while `Name`'s shape keeps its own.
    activate({ ...strings, stable: { excluded: [{ owner: "Literal", member: "type", text: "readonly type: UnitType.Literal;" }] } });
    const tagged = check(example("guards"), project);
    assert.equal(tagged.status, "verified", JSON.stringify(tagged));
    const shapes = must(readFragmentFile(join(tagged.artifacts, "fragment.json")).declarations, "the declarations").definitions
      .flatMap(d => d.expression?.k === "object" && d.expression.host !== undefined ? [{ name: d.declaration.name, term: d.expression }] : []);
    const residuals = shapes.filter(s => s.name.includes(" tags "));
    assert.ok(residuals.length > 0, "a residual arm");
    for (const r of residuals) assert.ok(!(r.term.stable ?? []).includes("type"), `${r.name}: no stable tag over an excluded one`);
    const name = must(shapes.find(s => s.name === "Name"), "the Name shape");
    assert.ok((name.term.stable ?? []).includes("type"), "Name's own tag stays stable");
    // An omitted member (HOST-FAMILIES.md, "The family contract"): the
    // description listing `Unit.notes`, the one thing changed, omits it from
    // every shape, so its read is refused; without the entry it verifies.
    activate(strings);
    const plain = check(example("notes"), project);
    assert.equal(plain.status, "verified", JSON.stringify(plain));
    activate({ ...strings, omitted: [{ owner: "Unit", member: "notes", text: "readonly notes: readonly string[];", why: "allocates" }] });
    const omitted = check(example("notes"), project);
    const notesAt = readFileSync(example("notes"), "utf8").lastIndexOf("u.notes");
    assert.ok(omitted.status !== "verified" && omitted.detail.includes(`at [${notesAt},`), JSON.stringify(omitted));
  } finally {
    useFamiliesForTests(null);
  }
  process.stdout.write("string-tagged family, activated by its description beside the compiler API's: its guards' calls are membership tests of string constants narrowing both edges, through a helper too; a guard outside the contract narrows nothing; its declarations of the compiler API's view names read as declared; its tag enum read as a value where its runtime object matches, refused over a copy whose runtime value differs and where Node binds the import to such a copy while TypeScript reads the audited declarations (Node returns it); a guard Node binds to another family's function, of the same name and domain, no guard (Node returns the excluded tag); a description of another digest or of an installation Node does not find refuses the run, and without the description nothing narrows; a stable member's test read past a call, refused where the description excludes the member; an excluded tag stable in no residual; an omitted member's read refused where the description lists it\n");
});

control("forged declarations: stable keys", async (): Promise<void> => {
  // Stable keys in the declaration document (HOST-FAMILIES.md, "Stable
  // keys"): the decoder accepts them as readonly members, required or
  // optional, of a marked family shape, and as required readonly fields of
  // an unmarked shape, a program record's. Each forged document is
  // refused by the decoder; its neighbour, differing in the one thing the
  // check reads, is decoded.
  const artifacts = run("compiler-api-path-witness");
  type Definition = TypeDefinition;
  type ObjectTerm = Extract<TypeTerm, { k: "object" }>;
  const shapeOf = (d: Definition): ObjectTerm => {
    const e = d.expression;
    assert(e?.k === "object");
    return e;
  };
  const searchWith = (file: string, change: (o: ObjectTerm) => void): string => {
    const fragment: Ast = fragmentAst(artifacts);
    const definition = must(must(fragment.declarations, "the declarations").definitions.find(d =>
      d.expression?.k === "object" && d.expression.host !== undefined && (d.expression.stable ?? []).length > 1 &&
      d.expression.fields.some(f => f.name === "text")), "a marked shape with stable keys");
    change(shapeOf(definition));
    return words(pass(forged(artifacts, file, fragment)));
  };
  const decoder = /stable key/;
  const honestWords = searchWith("stable-honest", () => {});
  assert.doesNotMatch(honestWords, decoder, honestWords);
  // A writable member stated stable, optional and required; the neighbour
  // of each states the member readonly, which the optional one is decoded
  // as too.
  const writable = searchWith("forged-stable-writable", o => {
    const text = must(o.fields.find(f => f.name === "text"), "text");
    text.optional = true;
    text.readonly = false;
  });
  assert.match(writable, /the stable key "text" is no readonly member of its shape/, writable);
  const writableRequired = searchWith("forged-stable-writable-required", o => {
    must(o.fields.find(f => f.name === "text"), "text").readonly = false;
  });
  assert.match(writableRequired, /the stable key "text" is no readonly member of its shape/, writableRequired);
  const optionalNeighbour = searchWith("stable-optional-neighbour", o => {
    must(o.fields.find(f => f.name === "text"), "text").optional = true;
  });
  assert.doesNotMatch(optionalNeighbour, decoder, optionalNeighbour);
  // A key the shape does not state; its neighbour states the member.
  const absent = searchWith("forged-stable-absent", o => { o.stable = [...(o.stable ?? []), "noSuchMember"]; });
  assert.match(absent, /the stable key "noSuchMember" is no readonly member of its shape/, absent);
  const absentNeighbour = searchWith("stable-absent-neighbour", o => {
    const text = must(o.fields.find(f => f.name === "text"), "text");
    o.fields.push({ ...text, name: "noSuchMember" });
    o.stable = [...(o.stable ?? []), "noSuchMember"];
  });
  assert.doesNotMatch(absentNeighbour, decoder, absentNeighbour);
  // An unmarked shape, a program record's, stating an optional readonly
  // member stable and a writable one; its neighbours state a required
  // readonly field stable, and none.
  const programRecord = /a program record's stable key is a required readonly field/;
  const unmarkedOptional = searchWith("forged-stable-unmarked-optional", o => {
    delete o.host;
    o.stable = ["text"];
    must(o.fields.find(f => f.name === "text"), "text").optional = true;
  });
  assert.match(unmarkedOptional, programRecord, unmarkedOptional);
  const unmarkedWritable = searchWith("forged-stable-unmarked-writable", o => {
    delete o.host;
    o.stable = ["text"];
    must(o.fields.find(f => f.name === "text"), "text").readonly = false;
  });
  assert.match(unmarkedWritable, programRecord, unmarkedWritable);
  const unmarkedRequired = searchWith("stable-unmarked-required", o => { delete o.host; o.stable = ["text"]; });
  assert.doesNotMatch(unmarkedRequired, decoder, unmarkedRequired);
  const unmarkedNeighbour = searchWith("stable-unmarked-neighbour", o => { delete o.host; delete o.stable; });
  assert.doesNotMatch(unmarkedNeighbour, decoder, unmarkedNeighbour);
  say("stable keys: a writable (optional and required), an absent and an unmarked optional or writable stable key refused by the decoder, each beside its decoded neighbour, an optional readonly one of a marked shape and a required readonly one of an unmarked shape decoded");
});


control("forged declarations: a stable link's key dropped", async (): Promise<void> => {
  // Stable links (HOST-FAMILIES.md, "Stable links"): a read link through a
  // member every arm states stable survives a call. The positive case's
  // document with the tested member's stable key dropped from its shape,
  // the one thing the rule reads, is refused by the pass at the read past
  // the call; the honest document is accepted.
  const artifacts = run("compiler-api-stable-link");
  const forged = (file: string, keys: (stable: readonly string[]) => string[] | undefined): string => {
    const fragment: Ast = fragmentAst(artifacts);
    for (const d of must(fragment.declarations, "the declarations").definitions) {
      const e = d.expression;
      if (e?.k !== "object" || e.host === undefined || e.stable === undefined) continue;
      if (!e.fields.some(f => f.name === "initializer")) continue;
      const next = keys(e.stable);
      if (next && next.length) e.stable = next;
      else delete e.stable;
    }
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    return path;
  };
  const honest = forged("stable-link-honest", s => [...s]);
  const honestPass = pass(honest);
  assert.ok(honestPass.status === 0 && [...honestPass.verdicts.values()].every((v) => v.closed), words(honestPass).slice(0, 1500));
  // Refused at a unit the honest document accepts, at the read past the call.
  const unstable = forged("forged-stable-link", s => s.filter(k => k !== "name"));
  const p = pass(unstable);
  refusedFile(p, "forged-stable-link", /obligation at \[\d+,\d+\)/);
  say("stable links: the document without the tested member's stable key refused in search and in checking, the honest one accepted");
});


control("forged declarations: stable optional members' keys dropped", async (): Promise<void> => {
  // Stable optional members (HOST-FAMILIES.md, "Stable keys"): the read of
  // an optional member past a call, absent or present, rests on the member's
  // stable key alone. The positive case's document with `initializer` and
  // `expression` dropped from the stable keys of the shapes stating them, the
  // one thing the rule reads, is refused by the pass; the honest document
  // is accepted.
  const artifacts = run("compiler-api-stable-optional");
  const forged = (file: string, keep: (key: string) => boolean): string => {
    const fragment: Ast = fragmentAst(artifacts);
    for (const d of must(fragment.declarations, "the declarations").definitions) {
      const e = d.expression;
      if (e?.k !== "object" || e.host === undefined || e.stable === undefined) continue;
      const next = e.stable.filter(keep);
      if (next.length) e.stable = next;
      else delete e.stable;
    }
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    return path;
  };
  const honest = forged("stable-optional-honest", () => true);
  const honestPass = pass(honest);
  assert.ok(honestPass.status === 0 && [...honestPass.verdicts.values()].every((v) => v.closed), words(honestPass).slice(0, 1500));
  // Refused at a unit the honest document accepts, at the read past the call.
  const unstable = forged("forged-stable-optional", k => k !== "initializer" && k !== "expression");
  const p = pass(unstable);
  refusedFile(p, "forged-stable-optional", /obligation at \[\d+,\d+\)|expression at node \d+: Verification\.Tm\.var/);
  say("stable optional members: the document without the optional members' stable keys refused in search and in checking, the honest one accepted");
});


// ---------------------------------------------------------------------------
// The stage store on the route: in a fresh store of the control's own.

control("forged fragment: a spine separation removed", async (): Promise<void> => {
  // A spine separation forged away in the fragment: `measure`'s precondition
  // `flags !== runs.openBrackets` removed, so `i < flags.length` is not kept
  // across `readRuns`, whose frame may change `runs.openBrackets`'s spine,
  // and the read `flags[i]` is refused.
  const artifacts = run("invalid-stated-alias");
  const ast = fragmentAst(artifacts);
  const measure = must(ast.functions.find((f) => f.name === "measure"), "measure");
  const unit = unitOf(ast, "measure");
  honest("invalid-stated-alias", unit);
  assert.ok(measure.requires.some((f) => "spineApart" in f), "measure states its separation");
  measure.requires = [];
  refused(pass(forged(artifacts, "forged-unseparated", ast)), unit, "forged");
  say("spine separations: the fragment without the callee's separation refused at the read it kept");
});

// ---------------------------------------------------------------------------
// Forged effects: a document's serialized effect forged, refused where the
// verifier reads it (REQUEST-PROTOCOL.md, "The serialized effect").

/** A case's fragment as parsed JSON, outside its declared shape: a forgery
 * may leave the grammar. */
function fragmentJson(artifacts: string): Record<string, unknown> {
  const value: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
  assert.ok(isObject(value), "a fragment");
  return value;
}
/** Whether an object is a serialized effect: its four fields. */
const isEffect = (node: Record<string, unknown>): boolean =>
  "exits" in node && "promise" in node && "requires" in node && "pre" in node;

control("forged effect: an exact write's range removed from its preconditions", async (): Promise<void> => {
  // `%ByteSet%`'s signatures state View-Write at their view's format and
  // their range as postconditions read at the entry; the forgery keeps
  // those postconditions and removes the preconditions that state the range,
  // so no caller would establish it. The verifier refuses the contract where
  // it reads it.
  const file = "typed-array-element-writes";
  const artifacts = run(file);
  honest(file, "writeThenRead@861");
  const document = fragmentJson(artifacts);
  let forgedCount = 0;
  visitAll(document, (node) => {
    if (isEffect(node) && (JSON.stringify(node.exits) ?? "").includes('"viewWrite":{"x":1,"i":2,"v":3,"format":"')) {
      node.pre = [];
      forgedCount++;
    }
  });
  assert.ok(forgedCount > 0, "an exact write's contract");
  refused(pass(forged(artifacts, "exact-write-range-removed", document)), "writeThenRead@861",
    "an exact write without its range among its preconditions",
    /an exact element write states its range among its preconditions/);
  say(`forged effect: ${forgedCount} exact writes without their range among their preconditions refused at their read`);
});

/** Require a forged fragment refused where the verifier reads it: by an
 * interface stage, which stops the run, or by the pass, at `at`. */
function refusedAtRead(fragment: string, unit: string, what: string, at: RegExp): void {
  let p: Pass;
  try {
    p = pass(fragment);
  } catch (error: unknown) {
    assert.match(error instanceof Error ? error.message : String(error), at, `${what}: refused otherwise`);
    return;
  }
  refused(p, unit, what, at);
}
control("forged effect: a key stated twice, once escaped", async (): Promise<void> => {
  // An effect's `pre` stated a second time as `"\u0070re"`: a reader of
  // objects into maps would keep one of the two. The document's text is
  // refused before it is read into maps, the keys compared as the strings
  // they state.
  const file = "typed-array-element-writes";
  const artifacts = run(file);
  const text = readFileSync(fragmentOf(artifacts), "utf8");
  const at = text.indexOf('"pre":[');
  assert.ok(at >= 0, "an effect's preconditions");
  const path = join(artifacts, "escaped-duplicate-key.json");
  writeFileSync(path, `${text.slice(0, at)}"\\u0070re":[],${text.slice(at)}`);
  refusedAtRead(path, "writeThenRead@861", "an escaped key stated twice", /an object states the key 'pre' twice/);
  say("forged effect: a key stated twice, once escaped, refused when the document's text is read");
});

control("forged effect: documents outside the grammar", async (): Promise<void> => {
  // A declaration's effect forged out of the serialized grammar, each
  // refused where the verifier reads it: a field no effect has at depth, an
  // assertion-arena reference, a transport's override that is no pair, a
  // second constructor tag, an integer as a string in the safe range; and a
  // statement whose exits state a postcondition no statement states.
  const file = "typed-array-element-writes";
  const unit = "writeThenRead@861";
  const artifacts = run(file);
  honest(file, unit);
  const forgeries: [string, (e: Record<string, unknown>) => void, RegExp][] = [
    ["nested-unknown-field", (e) => {
      const frame = isObject(e.exits) && isObject(e.exits.normal) && Array.isArray(e.exits.normal.frame) ? e.exits.normal.frame : [];
      const entry: unknown = frame[0];
      assert.ok(isObject(entry), "a frame entry");
      entry.extra = 1;
    }, /differs from its writing at \/exits\/normal\/frame\[0\]\/extra: a field the effect does not have/],
    ["arena-reference", (e) => ensuresOf(e).push({ and: { left: "truth", right: { at: { phase: "after", assertion: { index: 0 } } } } }),
      /exits\/normal\/ensures\/\[\d+\]\/and\/right\/at\/no formula of a specification/],
    ["malformed-transport", (e) => ensuresOf(e).push({ transport: { shift: 1, overrides: [[1]], boxed: false, stable: [] } }),
      /transport\/overrides\/\[0\]\/a pair is a list of two/],
    ["second-tag", (e) => ensuresOf(e).push({ and: { left: "truth", right: "truth" }, truth: null }),
      /a constructor is an object of one field, its name/],
    ["noncanonical-integer", (e) => { if (Array.isArray(e.pre)) e.pre.push({ index: { slot: "5" } }); },
      /differs from its writing at \/pre\[\d+\]\/index\/slot/],
  ];
  for (const [name, forge, at] of forgeries) {
    const document = fragmentJson(artifacts);
    let first = true;
    visitAll(document, (node) => {
      if (!first || !isEffect(node)) return;
      forge(node);
      first = false;
    });
    assert.ok(!first, "an effect");
    refusedAtRead(forged(artifacts, `effect-${name}`, document), unit, name, at);
  }
  const stated = run("stated-fresh");
  const statedDocument = fragmentJson(stated);
  const functions = Array.isArray(statedDocument.functions) ? statedDocument.functions : [];
  const same: unknown = functions.find((f: unknown) => isObject(f) && f.name === "same");
  assert.ok(isObject(same) && isObject(same.stated) === false, "same states nothing");
  same.stated = statedExits({ footprint: { value: "any", spine: "any" }, onThrow: false, fresh: false, regions: [] });
  const exits: unknown = same.stated;
  assert.ok(isObject(exits) && isObject(exits.normal) && Array.isArray(exits.normal.ensures));
  exits.normal.ensures.push("truth");
  refusedAtRead(forged(stated, "statement-outside-its-form", statedDocument), unitOf(fragmentAst(stated), "same"),
    "a statement stating a postcondition", /a statement states a closed frame with spine regions, a throw within it or none, and a fresh result/);
  say(`forged effect: ${forgeries.length} effects outside the grammar and a statement outside its form refused at their read`);
});
/** An effect's normal postconditions. */
function ensuresOf(e: Record<string, unknown>): unknown[] {
  assert.ok(isObject(e.exits) && isObject(e.exits.normal) && Array.isArray(e.exits.normal.ensures), "an effect's postconditions");
  return e.exits.normal.ensures;
}

control("forged effect: a noncanonical transport at coverage", async (): Promise<void> => {
  // `map(Number)`: `Number`'s call signature covers `map`'s callback's
  // (`Effect.covers`). `Number`'s effect given a transport postcondition
  // of shift 1, a canonical one, is still covered; of shift 2, which the
  // decoder reads but coverage's completion lemmas do not admit, the
  // coverage is refused: the call `version.split(".").map(Number)` finds
  // no derivation of its claim, the two documents differing in the shift
  // alone.
  const file = "number-value";
  const unit = "parts@230";
  const artifacts = run(file);
  honest(file, unit);
  const withTransport = (shift: number): Record<string, unknown> => {
    const document = fragmentJson(artifacts);
    const declarations = isObject(document.declarations) && Array.isArray(document.declarations.definitions)
      ? document.declarations.definitions : [];
    const number: unknown = declarations.find((d: unknown) => isObject(d) && isObject(d.declaration) && d.declaration.name === "Number");
    let forgedCount = 0;
    visitAll(isObject(number) ? number.expression : null, (node) => {
      if (!isEffect(node)) return;
      ensuresOf(node).push({ transport: { shift, overrides: [], boxed: false, stable: [] } });
      forgedCount++;
    });
    assert.ok(forgedCount > 0, "Number's call signature");
    return document;
  };
  accepted(pass(forged(artifacts, "transport-canonical", withTransport(1))), unit, "a canonical transport");
  refused(pass(forged(artifacts, "transport-noncanonical", withTransport(2))), unit, "a transport of shift 2",
    /source expression obligation at \[274,304\): evidence search failed: no derivation of its node-typing claim/);
  say("forged effect: Number's signature with a canonical transport covers map's callback; with a transport of shift 2 the coverage is refused");
});

control("forged effect: a rest closure's statement past its scope or through a path", async (): Promise<void> => {
  // A stated closure collecting a rest array, `sum = (...ns) => …`, is
  // checked after its prologue allocates the rest, so its signature's frames
  // read the heap at each location alone (`framesAtLocation`, the
  // allocation's stability). Its statement re-stated as written is
  // accepted.
  const file = "method-effect-rest";
  const artifacts = run(file);
  const restate = (regions: SpineRegion[]): Record<string, unknown> => {
    const document = fragmentJson(artifacts);
    let stated = 0;
    visitAll(document, (node) => {
      if (node.k !== "lambda" || !isObject(node.stated)) return;
      node.stated = statedExits({ footprint: { value: "keep", spine: "keep" }, onThrow: false, fresh: false, regions });
      stated++;
    });
    assert.equal(stated, 1, "sum's statement");
    return document;
  };
  const honestRun = pass(forged(artifacts, "rest-body-restated", restate([])));
  const units = [...honestRun.verdicts].filter(([, v]) => v.closed).map(([u]) => u);
  assert.ok(units.length > 0 && [...honestRun.verdicts.values()].every((v) => v.closed), `restated: ${words(honestRun).slice(0, 1500)}`);
  // Regions at the receiver, in scope at every arity: its own spine, read
  // at a location, is accepted; the spine of its field `f`, read through
  // the path, is refused at the code's obligations, where the two differ
  // only in reading the heap at a location (`framesAtLocation`).
  const own = pass(forged(artifacts, "rest-body-own-region", restate([{ position: 0, path: [], key: "[]", change: "any" }])));
  accepted(own, "init", "a region read at a location");
  // A region at a position past the closure's arity, read at a location:
  // the code's scope (`Effect.belowRow`) refuses it.
  refused(pass(forged(artifacts, "rest-body-far-region", restate([{ position: 5, path: [], key: "[]", change: "any" }]))), "init",
    "a region past the arity", /single pass: refused: code 0: its signature/);
  const p = pass(forged(artifacts, "rest-body-path-region", restate([{ position: 0, path: ["f"], key: "[]", change: "any" }])));
  refused(p, "init", "a rest body stated with a spine region", /single pass: refused: code 0: its signature/);

  say(`forged effect: a rest closure's statement re-stated accepted (${units.join(", ")}), with a region at a location accepted, with one past its arity or through a path refused at its code`);
});

/** The documents of a fragment: its own and each module's it carries. */
function documentsOf(fragment: Record<string, unknown>): Record<string, unknown>[] {
  const modules = Array.isArray(fragment.modules) ? fragment.modules.filter(isObject) : [];
  return [fragment, ...modules];
}
/** The index of the unique symbol `name` in a document's `symbols`. */
function symbolIndex(document: Record<string, unknown>, name: string): number {
  const symbols = isObject(document.declarations) && Array.isArray(document.declarations.symbols) ? document.declarations.symbols : [];
  const i = symbols.findIndex((s: unknown) => isObject(s) && s.name === name);
  assert.ok(i >= 0, `the symbol ${name}`);
  return i;
}
/** Add `entry` to the normal frame of every effect of the definition
 * `name` of a document. */
function addToFrames(document: Record<string, unknown>, name: string, entry: unknown): number {
  const definitions = isObject(document.declarations) && Array.isArray(document.declarations.definitions)
    ? document.declarations.definitions : [];
  const definition: unknown = definitions.find((d: unknown) => isObject(d) && isObject(d.declaration) && d.declaration.name === name);
  let added = 0;
  visitAll(definition, (node) => {
    if (!isEffect(node) || !isObject(node.exits) || !isObject(node.exits.normal) || !Array.isArray(node.exits.normal.frame)) return;
    node.exits.normal.frame.push(structuredClone(entry));
    added++;
  });
  assert.ok(added > 0, `an effect of ${name}`);
  return added;
}

control("forged effect: symbol identities read against their document's symbols", async (): Promise<void> => {
  // The importer and its module list their unique symbols in different
  // orders. `Map`'s effects, in both documents, are given a frame entry on
  // the receiver's field keyed by `Symbol.toStringTag`, each document naming
  // it by its own index: read at canonical numbers, the two stores agree
  // and the import is read as before. The importer naming another symbol
  // (`Symbol.toPrimitive`) there makes the stores differ, refused at the
  // read. A symbol key past its document's `symbols`, and a symbol literal
  // at a number no declared symbol has, are refused where the document is
  // read.
  const file = "interface-rows-symbol-order-value-import";
  const unit = "widest@912";
  const artifacts = run(file);
  honest(file, unit);
  const keyed = (document: Record<string, unknown>, name: string): unknown =>
    ({ region: { field: { x: 0, key: { symbol: symbolIndex(document, name) } } }, change: "keep" });
  const agreeing = fragmentJson(artifacts);
  const [importer, module] = documentsOf(agreeing);
  assert.ok(importer !== undefined && module !== undefined, "an importer and its module");
  assert.notEqual(symbolIndex(importer, "toStringTag"), symbolIndex(module, "toStringTag"), "two orders");
  for (const d of [importer, module]) addToFrames(d, "Map", keyed(d, "toStringTag"));
  accepted(pass(forged(artifacts, "symbol-order-agreeing", agreeing)), unit, "one symbol at two indices");
  const differing = fragmentJson(artifacts);
  const [importer2, module2] = documentsOf(differing);
  assert.ok(importer2 !== undefined && module2 !== undefined);
  addToFrames(importer2, "Map", keyed(importer2, "toPrimitive"));
  addToFrames(module2, "Map", keyed(module2, "toStringTag"));
  refused(pass(forged(artifacts, "symbol-order-differing", differing)), unit, "two symbols");
  const past = fragmentJson(artifacts);
  const [importer3] = documentsOf(past);
  assert.ok(importer3 !== undefined && isObject(importer3.declarations) && Array.isArray(importer3.declarations.symbols));
  const count = importer3.declarations.symbols.length;
  addToFrames(importer3, "Map", { region: { field: { x: 0, key: { symbol: count } } }, change: "keep" });
  refusedAtRead(forged(artifacts, "symbol-undeclared-key", past), unit, "a symbol key past the document's symbols",
    new RegExp(`a symbol key ${count} names no unique symbol its document declares`));
  const literal = fragmentJson(artifacts);
  const [importer4] = documentsOf(literal);
  assert.ok(importer4 !== undefined);
  const undeclared = 2 ** 40 + 7;
  let literals = 0;
  visitAll(importer4, (node) => {
    if (literals > 0 || !isEffect(node) || !isObject(node.exits) || !isObject(node.exits.normal) || !Array.isArray(node.exits.normal.ensures)) return;
    node.exits.normal.ensures.push({ operation: { post: { elementsWhen: { x: 0, value: { sym: { id: undeclared } }, y: 0, predicate: [] } } } });
    literals++;
  });
  assert.equal(literals, 1, "an effect of the importer");
  refusedAtRead(forged(artifacts, "symbol-undeclared-literal", literal), unit, "a symbol literal no document declares",
    new RegExp(`a symbol literal ${undeclared} is the canonical number of no unique symbol its document declares`));
  // An identity written as a decimal string, which the effect codec reads
  // as a natural number beyond the safe range: refused, as a key and as a
  // literal.
  const big = "9007199254740992";
  const stringKey = fragmentJson(artifacts);
  const [importer5] = documentsOf(stringKey);
  assert.ok(importer5 !== undefined);
  addToFrames(importer5, "Map", { region: { field: { x: 0, key: { symbol: big } } }, change: "keep" });
  refusedAtRead(forged(artifacts, "symbol-string-key", stringKey), unit, "a symbol key written as a string",
    new RegExp(`a symbol key '${big}' is written as a string`));
  const stringLiteral = fragmentJson(artifacts);
  const [importer6] = documentsOf(stringLiteral);
  assert.ok(importer6 !== undefined);
  let stringLiterals = 0;
  visitAll(importer6, (node) => {
    if (stringLiterals > 0 || !isEffect(node)) return;
    ensuresOf(node).push({ operation: { post: { elementsWhen: { x: 0, value: { sym: { id: big } }, y: 0, predicate: [] } } } });
    stringLiterals++;
  });
  assert.equal(stringLiterals, 1, "an effect of the importer");
  refusedAtRead(forged(artifacts, "symbol-string-literal", stringLiteral), unit, "a symbol literal written as a string",
    new RegExp(`a symbol literal '${big}' is written as a string`));
  say("symbol identities: one symbol at two documents' indices agrees, two symbols differ, an undeclared key and literal, and a key and literal written as strings refused at the read");
});

control("forged fragment: the rest intrinsic's effect widened", async (): Promise<void> => {
  // Rest collection consumes the intrinsic's stated effect, so the intrinsic at an
  // ordinary arrow's effect leaves the defining unit's growth footprint
  // unestablished.
  const artifacts = run("blocker-next-array-rest-footprint");
  const ast = fragmentAst(artifacts);
  const rest = must(ast.declarations.values.find((v) => v.binding.local === "%RestFrom:1%"), "the rest intrinsic");
  assert.ok(rest.type.k === "function");
  const before = pass(fragmentOf(artifacts));
  const units = [...before.verdicts].filter(([, v]) => v.closed).map(([u]) => u);
  assert.ok(units.length > 0, "the honest fragment accepts a unit");
  rest.type.effect = ordinaryEffect;
  const p = pass(forged(artifacts, "array-rest-unrestricted", ast));
  const lost = units.filter((u) => p.verdicts.get(u)?.closed !== true);
  assert.ok(lost.length > 0 || p.status !== 0 && p.verdicts.size === 0, `forged: no unit refused: ${words(p).slice(0, 2000)}`);
  say(`array rests: the rest intrinsic at an ordinary effect refuses ${lost.join(", ") || "the file"}`);
});

control("units: each listed with its dependencies, a names list selecting", async (): Promise<void> => {
  // The pass lists each
  // unit of module-cells with the units it depends on, the module's
  // initialization among them, and a names list checks those units alone.
  const artifacts = run("module-cells");
  const all = pass(fragmentOf(artifacts));
  const listed = [...all.verdicts.keys()];
  const id = (name: string): string => must(listed.find((u) => u.startsWith(`${name}@`)), `${name} listed: ${listed.join(", ")}`);
  for (const name of ["bump", "cached", "limited", "afterCall"]) accepted(all, id(name), "module-cells");
  const depends = (p: Pass, unit: string): string[] => {
    for (const line of p.stdout.split("\n").filter((l) => l.startsWith("{"))) {
      const v: unknown = JSON.parse(line);
      if (isObject(v) && v.unit === unit && Array.isArray(v.depends)) return v.depends.filter((d) => typeof d === "string");
    }
    return [];
  };
  const after = depends(all, id("afterCall"));
  assert.ok(after.includes(id("bump")), `afterCall depends on bump: ${after.join(", ")}`);
  assert.ok(depends(all, id("bump")).some((d) => !d.includes("@")), `bump depends on the initialization: ${depends(all, id("bump")).join(", ")}`);
  const one = pass(fragmentOf(artifacts), [], "bump");
  assert.deepEqual([...one.verdicts.keys()].filter((u) => u.includes("@")), [id("bump")], `bump alone: ${one.stdout}`);
  say("units: module-cells' units listed with their dependencies, the initialization among them; a names list checks bump alone");
});

control("forged fragment: a guard's undefined behaviour", async (): Promise<void> => {
  // A node guard on a `parent` that may be absent throws there, so both its edges
  // hold a present `parent`. Its behaviour on undefined forged unadmitted,
  // the test then reading `kind` of a value that may be absent, refuses
  // every unit reading through such a guard.
  const artifacts = run("compiler-api-guard-undefined");
  const before = pass(fragmentOf(artifacts));
  const units = [...before.verdicts].filter(([, v]) => v.closed).map(([u]) => u);
  assert.ok(units.length > 0, "the honest fragment accepts a unit");
  const ast = fragmentAst(artifacts);
  let forgedGuards = 0;
  visitAll(ast, (value) => {
    if (value.k === "tagMember" && value.onUndefined === "throws") { value.onUndefined = "unadmitted"; forgedGuards++; }
  });
  assert.ok(forgedGuards > 0, "a guard throwing on undefined");
  const p = pass(forged(artifacts, "guard-undefined-unadmitted", ast));
  const lost = units.filter((u) => p.verdicts.get(u)?.closed !== true);
  assert.ok(lost.length > 0 || p.status !== 0 && p.verdicts.size === 0,
    `forged: no unit refused: ${words(p).slice(0, 2000)}`);
  say(`guards on undefined: ${forgedGuards} guards forged unadmitted, refusing ${lost.join(", ") || "the file"}`);
});

control("forged fragment: a lone surrogate and bytes that are no UTF-8", async (): Promise<void> => {
  // A lone surrogate, which JSON writes as an escape, and bytes that are not UTF-8,
  // refused by Lean before it reads a value, and by TypeScript's reader.
  const artifacts = run("tag-set-code-points");
  const text = readFileSync(fragmentOf(artifacts), "utf8");
  assert.ok(text.includes(""), "the fragment holds U+E000");
  const lone = join(artifacts, "forged-lone-surrogate-fragment.json");
  writeFileSync(lone, text.replace("", "\\ud800"));
  assert.throws(() => readFragmentFile(lone), /not well-formed Unicode/);
  refusedFile(pass(lone), "a lone surrogate", /not well-formed Unicode/);
  const bytes = Buffer.from(text.replace("", "\u0001"), "utf8");
  const at = bytes.indexOf(0x01);
  assert.ok(at >= 0);
  bytes[at] = 0xff;
  const raw = join(artifacts, "forged-invalid-utf8-fragment.json");
  writeFileSync(raw, bytes);
  assert.throws(() => readFragmentFile(raw), /not valid UTF-8/);
  refusedFile(pass(raw), "bytes that are no UTF-8", /not valid UTF-8/);
  say("wire strings: the fragment with a lone surrogate or bytes that are no UTF-8 refused by Lean and TypeScript");
});

control("step failures: the pass's exit without a complete refusal is a tool failure", async (): Promise<void> => {
  // The pass's exit
  // other than its complete refusal record (exit 1, a first line `reject: …`
  // and a last line `end of refusal`) is a tool failure, no verdict: no
  // output, an exception's text, and a record cut short. The injected failure
  // is written into a stand-in the test process installs, so it is part of
  // the executable the invocation runs; a stand-in is no audited program, so
  // its invocation executes without a key.
  const dir = runDirectory("single-pass-step-failures-");
  const real = verifierBuild;
  let runs = 0;
  const outcomeOf = (text: string): Outcome => {
    const at = join(dir, `run-${runs++}`);
    mkdirSync(at);
    const stand = join(at, "verifier.sh");
    const quoted = `'${text.replaceAll("'", `'\\''`)}'`;
    writeFileSync(stand, `#!/bin/sh\nfor a in "$@"; do\n  if [ "$a" = "--file-worker" ]; then\n` +
      `    [ -n ${quoted} ] && echo ${quoted} >&2\n    exit 1\n  fi\ndone\nexec "${real}" "$@"\n`);
    chmodSync(stand, 0o755);
    const ran = spawnSync(process.execPath, [...standInOptions(at, stand),
      join(root, "pipeline/verify-source.mts"), join(root, "pipeline/examples/optional-chain-element-receiver.ts")],
      { encoding: "utf8", timeout: 120_000 });
    const outcome = readOutcome(JSON.parse(ran.stdout.slice(ran.stdout.indexOf("{"))));
    const failing = readInvocationLog(join(outcome.artifacts, invocationLog)).filter((r) => r.stage === "pass").at(-1);
    assert.ok(failing !== undefined && ranStage(failing) && failing.key === null, "the failing stage ran, without a key");
    return outcome;
  };
  for (const text of ["", "uncaught exception: forced by tests/single-pass-controls.mts", "reject: a record cut short"]) {
    const outcome = outcomeOf(text);
    assert.equal(outcome.status, "error", `${JSON.stringify(text)}: ${JSON.stringify(outcome)}`);
    assert.equal(outcome.detail,
      `tool failure: verifier --file-worker failed preparing the file: exited with status 1: ${text || "no output"}`);
  }
  // An operational failure of the verifier is its own exit status, 3.
  const unread = spawnSync(real, ["--verify-interface-stage", "8", join(dir, "absent.json"), join(dir, "absent.json"),
    "absent.ts", "12", ""], { encoding: "utf8" });
  assert.equal(unread.status, 3, unread.stderr);
  assert.match(unread.stderr, /^error: /);
  say("step failures: the pass's exit without a complete refusal is a tool failure; an unreadable input is the verifier's status 3");
});

infraControl("store: cold and warm runs, an importer's edit, over the interface stages", async (): Promise<void> => {
  const previous = process.env.TSCERT_STAGE_STORE;
  const scratch = runDirectory("single-pass-store-");
  const useStore = (name: string): void => {
    process.env.TSCERT_STAGE_STORE = join(scratch, name);
  };
  try {
    // An importer of certified.ts in a project of its own, so the control may edit it.
    const dir = join(scratch, "project");
    mkdirSync(dir);
    const certified = join(root, "pipeline/imports-project/certified.ts");
    writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noUncheckedIndexedAccess: true,
      module: "Node16", moduleResolution: "Node16", target: "ES2022", verbatimModuleSyntax: true, noEmit: true,
      paths: { "@fixture/certified": [certified] } }, include: ["*.ts", certified, join(root, "tools/resolvable.d.ts")] }));
    writeFileSync(join(dir, "package.json"), JSON.stringify({ type: "module" }));
    const importer = join(dir, "importer.ts");
    const text = readFileSync(join(root, "pipeline/examples/certified-value-import.ts"), "utf8");
    writeFileSync(importer, text);
    const records = (outcome: Outcome): { stage: string; execution: string }[] =>
      readInvocationLog(join(outcome.artifacts, invocationLog)).map((r) => ({ stage: r.stage, execution: r.execution }));
    const shape = (outcome: Outcome): string => JSON.stringify({ status: outcome.status,
      units: (outcome.units ?? []).map((u) => [u.unit, u.status, u.detail]) });
    useStore("first");
    const cold = check(importer, tsconfigOf(dir));
    assert.equal(cold.status, "verified", JSON.stringify(cold).slice(0, 1500));
    const warm = check(importer, tsconfigOf(dir));
    assert.equal(shape(warm), shape(cold), "warm and cold outcomes");
    const coldRecords = records(cold), warmRecords = records(warm);
    assert.ok(coldRecords.some((r) => r.execution === "executed"), JSON.stringify(coldRecords));
    assert.ok(warmRecords.length > 0 && warmRecords.every((r) => r.execution === "replayed"), JSON.stringify(warmRecords));
    // The interface stages, forced to run (`imports`): warm, replayed.
    const forcedRecords = (fragment: string): Invoked[] => {
      const work = runDirectory("single-pass-store-pass-");
      const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
      const { run, interfaces } = verifyWithInterfaces(fragment, isObject(ast) && typeof ast.file === "string" ? ast.file : "", "",
        { mode: 8, fuel: 12, rounds: 4096, force: ["imports"], work: join(work, "interfaces"),
          invocation: { limitMs: 60_000, force: false, recorder: null } });
      return [...interfaces.records, run];
    };
    const component = (rs: Invoked[]): Invoked[] => rs.filter((r) => r.record.stage === "module-interface");
    const firstForced = forcedRecords(fragmentOf(warm.artifacts));
    assert.ok(component(firstForced).length > 0, "a module-interface stage");
    assert.ok(forcedRecords(fragmentOf(warm.artifacts)).every((r) => r.record.execution === "replayed"), "forced, warm");
    // An edit of the importer: its parse and its importer stage execute; the module's interface replays.
    writeFileSync(importer, text + "\nexport function extra(): number {\n  return 1;\n}\n");
    const edited = check(importer, tsconfigOf(dir));
    const editedRecords = records(edited);
    assert.ok(editedRecords.some((r) => r.execution === "executed"), JSON.stringify(editedRecords));
    const editedForced = forcedRecords(fragmentOf(edited.artifacts));
    assert.ok(component(editedForced).every((r) => r.record.execution === "replayed"), "the module's interface replayed");
    assert.equal(must(editedForced.at(-1), "the importer stage").record.execution, "executed", "the importer stage executed");
    // Each outcome a cold run's, in a fresh store.
    useStore("second");
    const fresh = check(importer, tsconfigOf(dir));
    assert.equal(shape(fresh), shape(edited), "the edited outcome is a cold run's");
    assert.ok(records(fresh).some((r) => r.execution === "executed"));
  } finally {
    if (previous === undefined) delete process.env.TSCERT_STAGE_STORE;
    else process.env.TSCERT_STAGE_STORE = previous;
  }
  say("store: a warm run replays every stage to the cold outcome; the interface stages replay warm; an importer's edit executes its parse and importer stage, the module's interface replaying, to a cold run's outcome");
});

// ---------------------------------------------------------------------------
// Mutations of the pass: each check mutated to accept, a unit the production
// verifier refuses by that check accepted, so the control naming it is what
// catches the mutation.

mutationControl("sp-entry: the start's entry check, caught by the start-facts control", async (): Promise<void> => {
  const fragment = fragmentOf(run("returntype-guard"));
  refused(pass(fragment, ["start-facts"]), "isName@125", "production, forced start-facts");
  accepted(mutatedPass(fragment, "sp-entry", ["start-facts"]), "isName@125", "sp-entry, forced start-facts");
  say("mutation sp-entry: the false start facts accepted only without the entry check");
});

mutationControl("sp-footprint: the footprint check, caught by three negative cases", async (): Promise<void> => {
  for (const [file, unit] of [["invalid-method-effect-declaration", "bump@266"], ["invalid-sort-comparator-shrink", "sorted@301"],
      ["invalid-normal-return-catch", "wrong@94"]] as const) {
    const fragment = fragmentOf(run(file));
    refused(pass(fragment), unit, `${file} production`);
    accepted(mutatedPass(fragment, "sp-footprint"), unit, `${file} sp-footprint`);
  }
  say("mutation sp-footprint: a declaration's, a comparator's and a caught normal return's footprints exceeded, each accepted only without the footprint check");
});

// ---------------------------------------------------------------------------
// The parser's document and the driver: what the fragment states, a native
// counterexample under Node, run retention and replay.

control("string object hook: the counterexample under Node", async (): Promise<void> => {
  assert.equal(runExample("invalid-string-object-hook",
    '(() => { const cell = { value: "kept" }; return kept(cell, { a: 1, toString() { cell.value = undefined; return "object"; } }); })()'), undefined);
  say("string object hook: the counterexample's own toString writes the cell under Node");
});

control("imported functions left out with a function they read", async (): Promise<void> => {
  // Which functions of an imported module the parser keeps: `partial.ts`'s
  // `jumped` is refused, and each function reading it, directly, through
  // another, as a value, in a closure or in a parameter default, is left out
  // with it; a parameter of the same name is no read of it. A module whose
  // top-level code reads a function left out is listed with that code left
  // out: each name it binds absent, with the functions reading one.
  const partial = fragmentAst(run("invalid-absent-callee-value-import"));
  const [module] = partial.modules;
  assert.ok(module && partial.modules.length === 1 && module.location === "./partial.ts");
  assert.deepEqual(module.functions.map((f) => f.name), ["shadowed", "kept"]);
  const leftOut = (name: string, line: number, col: number): string =>
    `gate: a read of ${name}, a function of its module left out (line ${line}, col ${col})`;
  assert.deepEqual(module.absent.map((a) => [a.name, a.reason]), [
    ["jumped", "gate: statement outside the fragment (LastStatement) (line 8, col 3)"],
    ["relayed", leftOut("jumped", 13, 10)],
    ["passed", leftOut("jumped", 19, 17)],
    ["inClosure", leftOut("jumped", 22, 24)],
    ["defaulted", leftOut("jumped", 24, 50)],
    ["chained", leftOut("relayed", 16, 10)],
  ]);
  const [initModule] = fragmentAst(run("absent-init-value-import")).modules;
  assert.ok(initModule && initModule.location === "./partial-init.ts");
  assert.deepEqual(initModule.functions.map((f) => f.name), ["kept"]);
  assert.deepEqual(initModule.init, []);
  assert.deepEqual(initModule.absent.map((a) => [a.name, a.reason]), [
    ["start", "the module's top-level code is left out: gate: the module's top-level code reads jumped, a function of its module left out (line 13, col 30)"],
    ["jumped", "gate: statement outside the fragment (LastStatement) (line 6, col 3)"],
  ]);
  say("an imported module's functions reading a function left out: left out with it, transitively; a module whose top-level code reads one: listed with that code left out");
});

control("guard binding: a closure's write keeps the guard an ordinary call", async (): Promise<void> => {
  // A family guard is the inline membership test of a name only where no
  // write in its binding's scope names it (`unassigned`): a nested closure's
  // write keeps the guard an ordinary call; another function's write of its
  // own `e` does not.
  const lowered = (file: string): boolean => readFileSync(fragmentOf(run(file)), "utf8").includes('"tagMember"');
  assert.ok(lowered("compiler-api-guard-own-binding"),
    "compiler-api-guard-own-binding: the guard of a never-assigned binding is not the membership test");
  assert.ok(!lowered("compiler-api-guard-closure-write"),
    "compiler-api-guard-closure-write: the guard of a binding a closure assigns is the membership test");
  say("guard binding: a closure's write keeps the guard an ordinary call, another binding's does not");
});

control("tag selection: one per run", async (): Promise<void> => {
  // One tag selection per run (HOST-FAMILIES.md, "Residuals"): the importer
  // and the module it imports a function from name different kinds, and the
  // run reads every family declaration alike in both modules' documents,
  // the union of the kinds both name. The module's own run selects only its
  // own kinds.
  const ast = fragmentAst(run("compiler-api-units"));
  const [module] = ast.modules;
  const family = (definitions: readonly TypeDefinition[]): Map<string, TypeDefinition> => new Map(definitions
    .filter((d) => d.declaration.module.startsWith("tscert/family/") || d.declaration.module.includes("/typescript/dist/ast/"))
    .map((d) => [`${d.declaration.module}#${d.declaration.name}`, d]));
  const main = family(must(ast.declarations, "the importer's declarations").definitions);
  const imported = family(must(must(module, "the imported module").declarations, "its declarations").definitions);
  assert.deepEqual([...imported.keys()].sort(), [...main.keys()].sort(), "both documents read the same family declarations");
  for (const [key, definition] of main)
    assert.equal(JSON.stringify(imported.get(key)), JSON.stringify(definition), `${key} is read alike in both modules`);
  const arms = (definitions: Map<string, TypeDefinition>): number[] => {
    const node = [...definitions].find(([key]) => key.endsWith("/ast.d.ts#Node"));
    const expression = must(node, "Node's reading")[1].expression;
    assert.ok(expression?.k === "union", "Node's reading is a union");
    return expression.parts.map((part) => part.k !== "reference" ? -2
      : part.reference.name === "NumericLiteral" ? 9 : part.reference.name === "Identifier" ? 80 : -1);
  };
  assert.deepEqual(arms(main), [9, 80, -1], "the run's Node: NumericLiteral, Identifier and a residual");
  const project = join(root, "pipeline", "compiler-api-project");
  using alone = checkSource(join(project, "node-names.ts"), tsconfigOf(project), false, undefined, true);
  assert.equal(alone.status, "verified", JSON.stringify(alone));
  assert.deepEqual(arms(family(must(fragmentAst(alone.artifacts).declarations, "the module's declarations").definitions)), [80, -1],
    "the module's own run: Identifier and a residual");
  say("tag selection: one per run, the importer's and its module's family readings equal; the module's own run selects its own kinds");
});

infraControl("run retention: only requested runs are kept", async (): Promise<void> => {
  // A long-lived caller retains only explicitly requested runs, including
  // replayed results and results whose consumer throws.
  const source = join(root, "pipeline", "examples", "values.ts");
  for (let i = 0; i < 3; i++) {
    const result = checkSource(source);
    assert.equal(result.status, "verified");
    assert.equal(existsSync(result.artifacts), false);
  }
  let path = "";
  assert.throws(() => {
    using result = checkSource(source, undefined, false, undefined, true);
    path = result.artifacts;
    assert.ok(existsSync(join(path, "pass.log")));
    throw Error("consumer failed");
  }, /consumer failed/);
  assert.equal(existsSync(path), false);
  const module = pathToFileURL(join(root, "pipeline", "run-directory.mts")).href;
  const driver = pathToFileURL(join(root, "pipeline", "verify-source.mts")).href;
  // The driver is a file: a worker `checkApart` forks inherits the driver's
  // `execArgv`, where `--input-type` without `-e` stops it at its start.
  const failing = runDirectory("cleanup-control-");
  const failingDriver = join(failing, "driver.mts");
  writeFileSync(failingDriver, `
import assert from "node:assert/strict";
import fs from "node:fs";
import { syncBuiltinESMExports } from "node:module";
const { runRoot, runDirectory } = await import(${JSON.stringify(module)});
const root = runRoot();
const before = fs.readdirSync(root).sort();
const write = fs.writeFileSync;
fs.writeFileSync = (path, ...args) => {
  if (String(path).endsWith("request.json")) {
    runDirectory("nested-stage-");
    throw Error("injected request write failure");
  }
  return write(path, ...args);
};
syncBuiltinESMExports();
const { check, checkApart, RunFailure } = await import(${JSON.stringify(driver)});
assert.throws(() => check(${JSON.stringify(source)}), RunFailure);
assert.deepEqual(fs.readdirSync(root).sort(), before);
fs.writeFileSync = write;
syncBuiltinESMExports();
await assert.rejects(checkApart(${JSON.stringify(source)}), (e) => e instanceof RunFailure && e.message.startsWith("timeout: "));
assert.deepEqual(fs.readdirSync(root).sort(), before);
`);
  const failures = spawnSync(process.execPath, [failingDriver], { encoding: "utf8", timeout: 30_000,
    env: { ...process.env, TSCERT_STEP_LIMIT: "0.001", TSCERT_RUN_ROOT: failing } });
  assert.equal(failures.status, 0, failures.stderr);
  const tree = runDirectory("cleanup-tree-control-");
  const preload = join(tree, "preload.mjs");
  const driverFile = join(tree, "driver.mts");
  const armed = join(tree, "armed");
  writeFileSync(preload, `
import fs from "node:fs";
import { spawn } from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
const { runDirectory } = await import(${JSON.stringify(module)});
const write = fs.writeFileSync;
fs.writeFileSync = (path, ...args) => {
  if (String(path).endsWith("request.json")) {
    runDirectory("nested-stage-");
    spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], { stdio: ["ignore", "ignore", "inherit"] });
    write(${JSON.stringify(armed)}, "");
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0);
  }
  return write(path, ...args);
};
syncBuiltinESMExports();
`);
  writeFileSync(driverFile, `
import assert from "node:assert/strict";
import { existsSync, readdirSync } from "node:fs";
import { checkApart, RunFailure } from ${JSON.stringify(driver)};
const checked = checkApart(${JSON.stringify(source)});
// The check's timer cannot fire while this thread waits: the worker is
// stopped by it only once blocked, its child started.
const pause = new Int32Array(new SharedArrayBuffer(4));
while (!existsSync(${JSON.stringify(armed)})) Atomics.wait(pause, 0, 0, 10);
// The check settles at the worker's close, once every process holding its
// standard error, the child included, has ended.
await assert.rejects(checked, (e) => e instanceof RunFailure && e.message.startsWith("timeout: "));
assert.ok(existsSync(${JSON.stringify(armed)}));
assert.deepEqual(readdirSync(${JSON.stringify(tree)}).sort(), ["armed", "driver.mts", "preload.mjs"]);
`);
  const killedTree = spawnSync(process.execPath, ["--import", preload, driverFile], {
    encoding: "utf8", timeout: 60_000,
    env: { ...process.env, TSCERT_RUN_ROOT: tree, TSCERT_STEP_LIMIT: "0.5" },
  });
  assert.equal(killedTree.status, 0, killedTree.stderr);
  const low = spawnSync(process.execPath, ["--input-type=module", "-e", `
import fs from "node:fs";
import { syncBuiltinESMExports } from "node:module";
const { tmpdir } = await import("node:os");
const { join } = await import("node:path");
const stale = fs.mkdtempSync(join(tmpdir(), "tscert-runs-"));
fs.writeFileSync(join(stale, ".owner"), "2147483647");
delete process.env.TSCERT_RUN_ROOT;
fs.statfsSync = () => {
  if (fs.existsSync(stale)) throw Error("space checked before pruning");
  return { bavail: 0, bsize: 4096 };
};
syncBuiltinESMExports();
const { runDirectory } = await import(${JSON.stringify(module)});
runDirectory("must-not-start-");
`], { encoding: "utf8" });
  assert.equal(low.status, 1);
  assert.match(low.stderr, /TScert stopped: 0.00 GiB free.*at least 10 GiB required/);
  say("run retention: unrequested runs, a throwing consumer's, a failed request write's and a timed-out worker's left nothing; a run stops before it starts on a full disk");
});

infraControl("replay: cold, warm and evicted runs agree", async (): Promise<void> => {
  // Replay: a cold run in a fresh store and a warm run in another run root
  // agree on their outcome, documents and logs; the warm run replays every
  // stage (the module interfaces included), the parse by its observations.
  // The warm worker first checks other sources. After a pass evicting
  // everything, its source snapshots included, a run executes every stage
  // again to the same outcome, documents and logs. A changed source
  // executes again.
  const store = runDirectory("tscert-replay-store-");
  const runAt = (source: string, project: string | null, preceding: readonly string[] = []): { outcome: Outcome; records: AttemptRecord[] } => {
    const runs = runDirectory("tscert-replay-root-");
    // Sequential awaits use the same idle worker; each driver starts a fresh pool.
    const driver = `import { checkApart } from ${JSON.stringify(pathToFileURL(join(root, "pipeline", "verify-source.mts")).href)};
for (const source of ${JSON.stringify(preceding)}) await checkApart(source);
process.stdout.write(JSON.stringify(await checkApart(${JSON.stringify(source)}, ${JSON.stringify(project ?? undefined)}, false, undefined, true)));`;
    const driverPath = join(runs, "worker-history.mts");
    writeFileSync(driverPath, driver);
    const ran = spawnSync(process.execPath, [driverPath],
      { encoding: "utf8", timeout: 240_000, env: { ...process.env, TSCERT_STAGE_STORE: store, TSCERT_RUN_ROOT: runs } });
    assert.equal(ran.status, 0, ran.stderr);
    const outcome = readOutcome(JSON.parse(ran.stdout.slice(ran.stdout.indexOf("{"))));
    return { outcome, records: readInvocationLog(join(outcome.artifacts, invocationLog)) };
  };
  const documents = ["fragment.json", "parse.log", "pass.log", "typescript-diagnostics.json"];
  const contents = (artifacts: string): Map<string, string> => new Map(documents.flatMap((name): [string, string][] =>
    existsSync(join(artifacts, name)) ? [[name, readFileSync(join(artifacts, name), "utf8")]] : []));
  const replayed = new Set(["parse", "interface-plan", "module-interface", "pass", "diagnostics"]);
  const runs: [string, string | null][] = [["certified-nested-value-import", "pipeline/imports-project"],
    ["invalid-closure-contextual-result", null]];
  for (const [name, project] of runs) {
    const source = join(root, "pipeline", "examples", `${name}.ts`);
    const projectPath = project ? resolve(root, project) : null;
    const cold = runAt(source, projectPath), warm = runAt(source, projectPath,
      [join(root, "pipeline", "examples", "values.ts"), join(root, "pipeline", "examples", "invalid-void-result.ts")]);
    const { artifacts: coldArtifacts, ...coldOutcome } = cold.outcome;
    const { artifacts: warmArtifacts, ...warmOutcome } = warm.outcome;
    assert.notEqual(coldArtifacts, warmArtifacts);
    assert.deepEqual(warmOutcome, coldOutcome, `${name}: the same outcome`);
    assert.deepEqual(contents(warmArtifacts), contents(coldArtifacts), `${name}: the same documents and logs`);
    // A replayed parse runs no stage nested in it: its imported modules' stages ran in the cold run only.
    const outer = (records: readonly AttemptRecord[]): string[] => records.filter((r) => r.stage !== "module").map((r) => r.stage);
    assert.deepEqual(outer(warm.records), outer(cold.records), `${name}: the same stages`);
    assert.ok(project === null || cold.records.some((r) => r.stage === "module"), `${name}: its modules' stages ran cold`);
    for (const r of cold.records) assert.ok(ranStage(r), `${name}: cold ${r.stage} executed`);
    for (const r of warm.records) {
      assert.equal(r.execution, replayed.has(r.stage) && r.key !== null ? "replayed" : "executed", `${name}: warm ${r.stage}`);
      if (replayed.has(r.stage) && r.key === null) {
        assert.match(r.ineligible ?? "", /macOS and Linux only|Node import, require or loader|Node DYLD_|Node LD_|ld\.so\.preload|confined on macOS/,
          `${name}: ${r.stage} explains its unidentified dependencies`);
        say(`${name}: ${r.stage} executes without a key: ${r.ineligible}`);
      }
    }
    assert.ok(project === null || warm.records.some((r) => r.stage === "module-interface"), `${name}: module interfaces replayed`);
    // The drivers' worker processes hold their source snapshots until they stop.
    const stored = (part: string): number => existsSync(join(store, part)) ? readdirSync(join(store, part)).length : 0;
    // A platform where no stage has a key stores no entry (`ineligible`).
    if (cold.records.some((r) => r.key !== null))
      assert.ok(stored("sources") > 0 && stored("entries") > 0, `${name}: snapshots and entries stored`);
    else assert.equal(stored("entries"), 0, `${name}: no entry stored without keys`);
    let evictionPass = new Store(store).evictionPass(0);
    for (const started = Date.now(); evictionPass && evictionPass.held > 0 && Date.now() - started < 30_000;) {
      await new Promise((done) => setTimeout(done, 200));
      evictionPass = new Store(store).evictionPass(0);
    }
    assert.ok(evictionPass && evictionPass.afterBytes === 0 && stored("sources") === 0, JSON.stringify(evictionPass));
    assert.ok(readdirSync(join(store, "entries")).every((stage) => stored(join("entries", stage)) === 0), `${name}: no entry left`);
    const evicted = runAt(source, projectPath);
    const { artifacts: evictedArtifacts, ...evictedOutcome } = evicted.outcome;
    assert.deepEqual(evictedOutcome, coldOutcome, `${name}: the same outcome after eviction`);
    assert.deepEqual(contents(evictedArtifacts), contents(coldArtifacts), `${name}: the same documents and logs after eviction`);
    for (const r of evicted.records) assert.ok(ranStage(r), `${name}: ${r.stage} executed after eviction`);
  }
  const changed = join(runDirectory("tscert-replay-changed-"), "changed.ts");
  writeFileSync(changed, readFileSync(join(root, "pipeline", "examples", "values.ts"), "utf8") + "\n// changed\n");
  const before = runAt(join(root, "pipeline", "examples", "values.ts"), null);
  const after = runAt(changed, null);
  assert.equal(after.outcome.status, before.outcome.status);
  for (const r of after.records) assert.ok(ranStage(r), `a changed source: ${r.stage} executed`);
  // A file with modules: its interface stages run before any of its pass
  // stage's records, so its units are checked once, at those interfaces.
  const importing = runAt(join(root, "pipeline", "examples", "value-imports.ts"), resolve(root, "pipeline/imports-project"));
  assert.equal(importing.outcome.status, "verified", "value-imports verifies at its module interfaces");
  const stagesRun = importing.records.map((r) => r.stage);
  assert.ok(stagesRun.includes("interface-plan") && stagesRun.includes("pass") &&
    stagesRun.lastIndexOf("interface-plan") < stagesRun.indexOf("pass"),
    `value-imports: its interface stages, then its pass stage: ${JSON.stringify(stagesRun)}`);
  say("replay: cold and warm workers with different request histories agree on outcomes, documents and logs; the warm run " +
    "replays every stage, the parse by its observations, and executes stages with unidentified dependencies; after an eviction " +
    "every stage executes to the same outcome; a changed source executes its stages");
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
const infraTier = !serving && process.argv[2] === "--infra";
const chosen = process.argv.slice(serving ? 3 : infraTier ? 3 : 2);
if (serving) {
  // A control process: one control per message. A process whose caches may
  // disagree with the file system reports its control and exits.
  process.on("message", (message: unknown) => {
    if (!isObject(message) || typeof message.control !== "number" || !(message.mutated === null || typeof message.mutated === "string"))
      throw Error(`not a control's request: ${JSON.stringify(message)}`);
    const index = message.control;
    if (typeof message.mutated === "string") mutated = usePassMutationVerifier(message.mutated);
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
  // `node tests/single-pass-controls.mts [--infra] [pattern…]`: the controls
  // whose names contain a pattern, every one with none; the infrastructure's
  // with --infra, the others without.
  startEviction();
  linkFixtures();
  // In the infrastructure's tier with no pattern, the observed stages' replay controls
  // (tests/observed-stages.mts), which run their stages in fresh processes,
  // the parse's with real compilers, and the retained declaration sessions'
  // controls (tests/session-reuse.mts), each in a process of its own beside
  // the pool; their results are reported at its end.
  const beside = (module: string): Promise<{ status: number | null; stdout: string; stderr: string }> =>
    new Promise((done, fail) => {
      const child = spawn(process.execPath, [join(import.meta.dirname, module)], { stdio: ["ignore", "pipe", "pipe"] });
      let stdout = "", stderr = "";
      child.stdout.setEncoding("utf8");
      child.stderr.setEncoding("utf8");
      child.stdout.on("data", (text: unknown) => { stdout += String(text); });
      child.stderr.on("data", (text: unknown) => { stderr += String(text); });
      child.on("error", fail);
      child.on("close", (status: number | null) => done({ status, stdout, stderr }));
    });
  const besides = chosen.length > 0 || !infraTier ? [] : [beside("observed-stages.mts"), beside("session-reuse.mts")];
  const started = performance.now();
  const failures: string[] = [];
  const tally: Operations = { executed: 0, replayed: 0, elapsedMs: 0 };
  const withStops = process.env.TSCERT_SINGLE_PASS_STOPS === "1";
  const selected = controls.flatMap((c, i) => (withStops || !stops.has(i)) && infraControls.has(i) === infraTier &&
    (chosen.length === 0 || chosen.some((p) => c.name.includes(p))) ? [i] : []);
  const pending = selected.filter((i) => !mutationControls.has(i));
  // The pass's mutation verifier, built beside the other controls when a
  // selected control runs it; those controls join once it is built.
  let mutationPath: string | null = null;
  const waiting: (() => void)[] = [];
  const needsMutation = selected.some((i) => mutationControls.has(i));
  const mutationReady = !needsMutation ? Promise.resolve() : new Promise<void>((done, fail) => {
    const build = spawn(process.execPath, [join(import.meta.dirname, "single-pass-mutations.mts"), "--build",
      runDirectory("single-pass-mutations-")],
      { stdio: ["ignore", "pipe", "pipe"] });
    let out = "", err = "";
    build.stdout.setEncoding("utf8");
    build.stdout.on("data", (t: unknown) => { out += String(t); });
    build.stderr.setEncoding("utf8");
    build.stderr.on("data", (t: unknown) => { err += String(t); });
    build.on("error", fail);
    build.on("exit", (status: number | null) => {
      if (status !== 0) {
        fail(Error(`the pass's mutation verifier's build exited with ${status}: ${err}`));
        return;
      }
      mutationPath = must(out.trim().split("\n").at(-1), "the mutation verifier's path");
      pending.unshift(...selected.filter((i) => mutationControls.has(i)));
      for (const wake of waiting.splice(0)) wake();
      done();
    });
  });
  if (!withStops && !infraTier)
    for (const i of stops) process.stdout.write(`not run (TSCERT_SINGLE_PASS_STOPS=1 runs it): ${controls[i]?.name}\n`);
  const total = selected.length;
  let processes = 0;
  const width = Math.max(1, Math.min(availableParallelism(), selected.length));
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
      if (index !== undefined) child.send({ control: index, mutated: mutationPath });
      else if (needsMutation && mutationPath === null) waiting.push(give);
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
      if (retired && status === 0 && (pending.length > 0 || needsMutation && mutationPath === null)) lane().then(done, fail);
      else done();
    });
    give();
  });
  await Promise.all([mutationReady, ...Array.from({ length: width }, lane)]);
  for (const ran of await Promise.all(besides)) {
    if (ran.status !== 0) failures.push(ran.stdout + ran.stderr);
    else process.stdout.write(ran.stdout);
  }
  process.stdout.write(`controls: ${total} in ${((performance.now() - started) / 1000).toFixed(1)} s on ${width} ` +
    `lanes (${processes} processes); their operations ${tally.executed} executed (${(tally.elapsedMs / 1000).toFixed(1)} s ` +
    `in all), ${tally.replayed} replayed\n`);
  assert.deepEqual(failures, [], failures.join("\n"));
}
