// The controls of retained declaration sessions (STAGE-STORE.md, "Retained
// declaration sessions"), each through the production stage adapters
// (`parseCall`, `diagnosticsCall`, `invokeInProcess`) over a private copy of
// the value-import examples and their named project:
// - a parse in a reused session is byte for byte the parse in fresh
//   compilers at the same paths, refusals as well as successes, in forward,
//   reverse and A–B–A orders, and with distinct snapshot directories sharing
//   one resolution project; the session is opened once and reused, the
//   parser opened afresh by every parse; diagnostics between parses reuse it
//   and leave it clean;
// - another project, resolution directory, family configuration or an
//   automatically selected project replaces the session;
// - a dependency first read by a later collection enters the ledger and the
//   stored entry; changing it, or any answer of the ledger (a declaration, a
//   configuration, an absent target created, a directory's entries, a link,
//   a removed file) replaces the session and refuses the stored entry;
// - an incomplete read, a failed or unclean restoration (an overlay or a
//   second project left) publish nothing and release the session; a changed
//   Node answer makes the process inconsistent, to be retired;
// - the compiler's CPU time counted over attempts agrees with its lifetime's.
// Each control executes every time, in a store of its own.
import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { cpSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { compilerAccounts, invokeInProcess, Recorder, type AttemptRecord } from "../pipeline/stages.mts";
import { Store } from "../pipeline/stage-store.mts";
import { diagnosticsCall, parseCall, type Parsed } from "../pipeline/parse-stage.mts";
import { runnerBuild } from "../pipeline/stage-execution.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";
import { compilerApiFamily } from "../tools/compiler-api.mts";
import { useFamiliesForTests } from "../tools/family-activation.mts";
import { parserOpenings } from "../tools/fragment-parse.mts";
import { nodeResolve, processInconsistency, unobservable } from "../tools/files.mts";
import { liveCompilers } from "../tools/compiler-processes.mts";
import { asideForTests, declarationSessionTelemetry, injectSessionFaultForTests, retainDeclarationSessions, retainedDeclarationSession,
  retainedLedgerForTests } from "../tools/declaration-session.mts";
import type { SeenDiagnostic } from "../tools/declaration-graph.mts";

const here = import.meta.dirname;
const repository = resolve(here, "..");
const dir = runDirectory("tscert-sessions-");

/** A copy of the value-import examples beside the modules they import, in
 * one project directory, at `name`. */
function fixture(name: string): { examples: string; config: string } {
  const project = join(dir, name);
  cpSync(join(repository, "pipeline", "imports-project"), project, { recursive: true });
  for (const file of readdirSync(join(repository, "pipeline", "examples")).filter((f) => f.includes("value-import") && f.endsWith(".ts")))
    cpSync(join(repository, "pipeline", "examples", file), join(project, file));
  const config = join(project, "tsconfig.json");
  writeFileSync(config, readFileSync(config, "utf8").replace('"../examples/*value-import*.ts"', '"./*value-import*.ts"'));
  return { examples: project, config };
}

// The stores: every control names its own.
let stores: number = 0;
const useStore = (): string => {
  const root = join(dir, `store-${++stores}`);
  process.env["TSCERT_STAGE_STORE"] = root;
  return root;
};

/** A snapshot of an example's bytes in a directory of its own, as
 * `parseSource` makes one. */
function snapshot(examples: string, name: string, directory: string): { bytes: Buffer; file: string; resolution: string } {
  const resolution = join(examples, `${name}.ts`);
  const bytes = readFileSync(resolution);
  const at = join(dir, "snapshots", directory);
  mkdirSync(at, { recursive: true });
  writeFileSync(join(at, "source.ts"), bytes);
  writeFileSync(join(at, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true, target: "es2022" },
    files: ["source.ts", resolvableDeclaration] }));
  return { bytes, file: join(at, "source.ts"), resolution };
}

type Request = { name: string; directory: string; config: string | undefined; examples: string };
type Parse = { value: Parsed; record: AttemptRecord };
function parse(r: Request, force: boolean = true): Parse {
  const s = snapshot(r.examples, r.name, r.directory);
  return invokeInProcess(parseCall(s.bytes, s.file, r.config, r.config ? s.resolution : s.file),
    { force, recorder: new Recorder(null) });
}
/** The parse of `r` in fresh compilers: no session retained. */
function fresh(r: Request): Parsed {
  return asideForTests(() => parse(r).value);
}
const telemetry = declarationSessionTelemetry;
const generation = (): number | null => retainedDeclarationSession()?.generation ?? null;
/** The retained session's base state: its one project, no document, no overlay. */
function clean(config: string, what: string): void {
  const s = retainedDeclarationSession();
  assert.ok(s, `${what}: a session is retained`);
  assert.deepEqual(s.projects, [config], what);
  assert.equal(s.openDocuments, 0, what);
  assert.equal(s.overlay, 0, what);
}

useStore();
retainDeclarationSessions(true);
const base = fixture("base");

// A worker holding a session, killed while it computes: its compilers end
// with it.
if (process.argv[2] === "--hold") {
  parse({ name: "certified-value-import", directory: "hold", config: base.config, examples: base.examples });
  process.stdout.write(JSON.stringify(liveCompilers().map((c) => c.pid)) + "\n");
  for (;;);
}
{
  const held = spawn(process.execPath, [import.meta.filename, "--hold"], { stdio: ["ignore", "pipe", "inherit"] });
  const pids = await new Promise<number[]>((done, fail) => {
    let out = "";
    held.stdout.setEncoding("utf8");
    held.stdout.on("data", (text: unknown) => {
      out += String(text);
      if (!out.endsWith("\n")) return;
      const listed: unknown = JSON.parse(out);
      done(Array.isArray(listed) ? listed.filter((p: unknown): p is number => typeof p === "number") : []);
    });
    held.on("error", fail);
  });
  assert.ok(pids.length > 0, "the worker holds a compiler");
  held.kill("SIGTERM");
  const alive = (pid: number): boolean => {
    try {
      process.kill(pid, 0);
      return true;
    } catch {
      return false;
    }
  };
  const until = Date.now() + 10_000;
  while (pids.some(alive) && Date.now() < until) await new Promise((r) => setTimeout(r, 50));
  assert.deepEqual(pids.filter(alive), [], "the killed worker's compilers end");
}
const at = (name: string, directory: string = name): Request =>
  ({ name, directory, config: base.config, examples: base.examples });
// Successes, refusals at the gate and at the declaration graph.
const names = ["certified-value-import", "overload-value-import", "invalid-side-effect-value-import",
  "symbol-key-value-import", "invalid-symbol-key-missing-value-import", "default-import-value-import",
  "invalid-written-whole-class-value-import"];

// --- fidelity: every invocation against a fresh run at the same paths
const requests: Request[] = [
  ...names.map((n) => at(n)), // forward
  ...[...names].reverse().map((n) => at(n)), // reverse
  at(names[0], "a-again"), at(names[1], "b-again"), at(names[0], "a-again"), // A–B–A, distinct snapshot directories
];
const references = new Map<string, Parsed>();
const freshStarted = performance.now();
const key = (r: Request): string => `${r.directory}\0${r.name}`;
for (const r of requests) if (!references.has(key(r))) references.set(key(r), fresh(r));
const codes = new Set([...references.values()].map((p) => p.code));
assert.deepEqual([...codes].sort(), [0, 1], "the references hold successes and refusals");
const freshMs = performance.now() - freshStarted;
const reuseStarted = performance.now();
const before = telemetry();
const parsersBefore = parserOpenings();
let first: number | null = null;
for (const [i, r] of requests.entries()) {
  const parsers = parserOpenings();
  const done = parse(r);
  assert.deepEqual(done.value, references.get(key(r)), `${r.name} in ${r.directory}, invocation ${i}`);
  assert.equal(done.record.execution, "executed");
  assert.ok(parserOpenings() > parsers, `a fresh parser for invocation ${i}`);
  first ??= generation();
  assert.equal(generation(), first, `one session through invocation ${i}: ${JSON.stringify(telemetry())}`);
  clean(base.config, `after invocation ${i}`);
}
const reuseMs = performance.now() - reuseStarted;
const after = telemetry();
assert.equal(after.opens - before.opens, 1, "one declaration compiler opened");
assert.ok(after.reuses - before.reuses >= requests.length - 1, "every later collection reuses it");
assert.equal(after.replacements, before.replacements);
assert.ok(parserOpenings() - parsersBefore >= requests.length);

// --- TypeScript's diagnostics between parses reuse the session, clean
// before and after; the same as in a fresh compiler
for (const name of [names[0], names[3]]) {
  const file = join(base.examples, `${name}.ts`);
  const call = (): SeenDiagnostic[] => invokeInProcess(diagnosticsCall(file, base.config),
    { force: true, recorder: null }).value;
  const reference = asideForTests(call);
  parse(at(names[1]));
  clean(base.config, "before diagnostics");
  const was = telemetry(), session = generation();
  assert.deepEqual(call(), reference, `${name}: diagnostics`);
  clean(base.config, "after diagnostics");
  assert.equal(generation(), session, "diagnostics reuse the session");
  assert.equal(telemetry().opens, was.opens);
  assert.equal(telemetry().reuses, was.reuses + 1);
  assert.deepEqual(parse(at(name)).value, references.get(key(at(name))), `${name} after diagnostics`);
  assert.equal(generation(), session);
}

/** `r` parsed in the retained session or its replacement, the same as in
 * fresh compilers. */
function same(r: Request, what: string): Parse {
  const reference = fresh(r);
  const done = parse(r);
  assert.deepEqual(done.value, reference, what);
  return done;
}
/** `run` replaces the retained session: it is released, a compiler opened
 * for its successor, unless `automatic`, which keeps none. */
function replaces(what: string, run: () => void, automatic: boolean = false, exactly: boolean = true): void {
  const was = telemetry(), old = generation();
  assert.notEqual(old, null, `${what}: a session is retained before`);
  run();
  const now = telemetry();
  const replacements = now.replacements - was.replacements, opens = now.opens - was.opens;
  assert.ok(exactly ? replacements === 1 : replacements >= 1, `${what}: ${JSON.stringify(now)}`);
  assert.ok(exactly ? opens === (automatic ? 0 : 1) : opens === replacements, what);
  assert.notEqual(generation(), old, what);
}

// --- another project, resolution directory, family configuration or an
// automatically selected project replaces the session
const other = fixture("other");
replaces("another project", () => void same({ ...at(names[0]), config: other.config, examples: other.examples },
  "another project"));
same(at(names[0]), "back to the first project");
mkdirSync(join(base.examples, "sub"));
cpSync(join(base.examples, `${names[3]}.ts`), join(base.examples, "sub", `${names[3]}.ts`));
writeFileSync(base.config, readFileSync(base.config, "utf8").replace('"./*value-import*.ts"', '"./*value-import*.ts", "./sub/*.ts"'));
same(at(names[0]), "the project's configuration changed");
replaces("another resolution directory", () => void same({ ...at(names[3], "sub"), examples: join(base.examples, "sub") },
  "a resolution file in another directory"));
same(at(names[3]), "back to the first directory");
replaces("another family configuration", () => {
  useFamiliesForTests([{ ...compilerApiFamily, corrections: compilerApiFamily.corrections.slice(1) }]);
  try {
    same(at(names[0]), "another family configuration");
  } finally {
    useFamiliesForTests(null);
  }
});
same(at(names[0]), "the reviewed families again");
const automatic: Parse[] = [];
replaces("an automatically selected project", () => {
  automatic.push(same({ ...at(names[0], "automatic"), config: undefined }, "an automatically selected project"));
}, true);
assert.equal(retainedDeclarationSession(), null, "an automatically selected project retains no session");
assert.notDeepEqual(parse(at(names[0], "automatic")).record.manifest, automatic[0]?.record.manifest,
  "project selection is an input");

// --- same-path text replacement: a snapshot path given other bytes is
// another input, read in the same session
{
  const one = parse(at(names[0], "same-path"));
  const session = generation(), opens = telemetry().opens;
  const two = same(at(names[3], "same-path"), "another text at the same path");
  assert.notDeepEqual(one.record.manifest, two.record.manifest);
  assert.equal(generation(), session);
  assert.equal(telemetry().opens, opens);
}

// --- a dependency first read by a later collection: it enters the ledger and
// the stored entry; changing it replaces the session, and its entry no
// longer replays
const ledger = (): Map<string, string | null> => new Map(retainedLedgerForTests().map((n) =>
  [`${n.observation[0]} ${n.observation[1]}`, n.observation[2]]));
const observationsOf = (store: string, record: AttemptRecord): string[] => {
  assert.ok(record.key, `a stored entry: ${record.ineligible}`);
  const found = new Store(store).finished("parse", record.key, null);
  assert.ok(found, "the entry is stored");
  const input: unknown = JSON.parse(found.result.input);
  const listed = typeof input === "object" && input !== null && "observations" in input && Array.isArray(input.observations)
    ? input.observations : [];
  return listed.map((o: unknown) => Array.isArray(o) ? `${String(o[0])} ${String(o[1])}` : "");
};
{
  const storeOne = useStore();
  const later = fixture("later");
  const r = (name: string): Request => ({ name, directory: `later-${name}`, config: later.config, examples: later.examples });
  parse(r(names[0]));
  const known = ledger();
  const dependent = parse(r(names[1]));
  const found = [...ledger().keys()].filter((k) => !known.has(k) && k.startsWith("real ") && !k.endsWith(`${names[1]}.ts`));
  const d = found[0]?.slice("real ".length);
  assert.ok(d, `a dependency the later collection reads first: ${found.join(", ")}`);
  assert.ok(observationsOf(storeOne, dependent.record).includes(`real ${d}`), "the dependency is in the stored entry");
  // A warm replay opens no compiler and uses no session.
  const was = telemetry(), parsers = parserOpenings();
  const replayed = parse(r(names[1]), false);
  assert.equal(replayed.record.execution, "replayed");
  assert.deepEqual(telemetry(), was);
  assert.equal(parserOpenings(), parsers);
  // The same bytes through a link: only the real path answers otherwise.
  const elsewhere = join(dir, "elsewhere");
  mkdirSync(elsewhere, { recursive: true });
  cpSync(d, join(elsewhere, "dependency.ts"));
  rmSync(d);
  symlinkSync(join(elsewhere, "dependency.ts"), d);
  useStore();
  replaces("a changed dependency", () => void same(r(names[1]), "after the dependency changed"));
  assert.match(telemetry().lastReplacement ?? "", new RegExp(`real ${d}`));
  process.env["TSCERT_STAGE_STORE"] = storeOne;
  assert.equal(parse(r(names[1]), false).record.execution, "executed", "the entry no longer replays");
}

// --- any changed answer of the ledger replaces the session and refuses the
// stored entry
type Mutation = { what: string; mutate: (project: string, answers: Map<string, string | null>) => void };
const insideOf = (project: string): ((k: string) => string | null) => (k: string): string | null => {
  const path = k.slice(k.indexOf(" ") + 1);
  return path.startsWith(project + "/") ? path : null;
};
const mutations: Mutation[] = [
  { what: "a declaration read", mutate: (project) => writeFileSync(join(project, "lib.ts"),
    readFileSync(join(project, "lib.ts"), "utf8") + "\n// changed\n") },
  { what: "the configuration", mutate: (project) => writeFileSync(join(project, "tsconfig.json"),
    readFileSync(join(project, "tsconfig.json"), "utf8") + "\n") },
  { what: "an absent resolution target created", mutate: (project, answers) => {
    const absent = [...answers].filter(([k, v]) => v === null && k.startsWith("kind ")).map(([k]) => insideOf(project)(k))
      .find((p): p is string => p !== null);
    assert.ok(absent, "an absent target inside the project");
    mkdirSync(dirname(absent), { recursive: true });
    writeFileSync(absent, "export {};\n");
  } },
  { what: "a directory's entries", mutate: (project) => writeFileSync(join(project, "added.txt"), "added\n") },
  { what: "a link", mutate: (project, answers) => {
    const linked = [...answers.keys()].filter((k) => k.startsWith("real ")).map(insideOf(project))
      .find((p): p is string => p !== null && p.endsWith(".ts") && !p.endsWith(`${names[0]}.ts`));
    assert.ok(linked, "a file whose real path was read");
    const target = join(dir, "linked", `${project.split("/").pop() ?? ""}.ts`);
    mkdirSync(dirname(target), { recursive: true });
    renameSync(linked, target);
    symlinkSync(target, linked);
  } },
  { what: "a removed file", mutate: (project) => rmSync(join(project, "pong.ts")) },
];
for (const [i, m] of mutations.entries()) {
  const store = useStore();
  const changed = fixture(`changed-${i}`);
  const r: Request = { name: names[0], directory: `changed-${i}`, config: changed.config, examples: changed.examples };
  const stored = parse(r);
  assert.ok(stored.record.key, `${m.what}: published`);
  m.mutate(changed.examples, ledger());
  // A changed import's directory replaces the session once more.
  replaces(m.what, () => {
    const done = parse(r, false);
    assert.equal(done.record.execution, "executed", `${m.what}: the stored entry is refused`);
  }, false, false);
  assert.equal(new Store(store).finished("parse", stored.record.key ?? "", null) !== null, true, "the entry remains");
  same(r, `${m.what}: the replacement's parse`);
}

// --- an incomplete read, a failed or unclean restoration: nothing is
// published and the session is released
const released = (what: string, fault: Parameters<typeof injectSessionFaultForTests>[0], reason: RegExp): void => {
  useStore();
  parse(at(names[0]));
  const was = telemetry();
  injectSessionFaultForTests(fault);
  const done = parse(at(names[3]));
  injectSessionFaultForTests(null);
  assert.equal(done.record.key, null, `${what}: nothing is published`);
  assert.match(done.record.ineligible ?? "", reason, what);
  assert.deepEqual(done.value, references.get(key(at(names[3]))), `${what}: the attempt's value`);
  assert.equal(telemetry().discarded, was.discarded + 1, what);
  assert.equal(retainedDeclarationSession(), null, `${what}: the session is released`);
  const opens = telemetry().opens;
  same(at(names[0]), `${what}: the next parse`);
  assert.equal(telemetry().opens, opens + 1, `${what}: a new session`);
};
released("an incomplete read", { kind: "during", during: () => unobservable("an injected incomplete read") },
  /injected incomplete read/);
released("a failed restoration", { kind: "restoration" }, /restoration failed: an injected restoration failure/);
released("an overlay left", { kind: "overlay" }, /restoration failed: the session's overlay is not empty/);
released("a second project left", { kind: "project", project: other.config }, /restoration failed: the session holds the projects/);

// --- the compiler's CPU time: the attempts' readings of a retained session
// sum to its lifetime's but its idle time
{
  const session = liveCompilers().at(-1);
  assert.ok(session && generation() !== null);
  const p = spawnSync(runnerBuild, ["--cpu", String(session.pid)], { encoding: "utf8" });
  const used = /^cpu (\d+) (\d+) (\d+)\n$/.exec(p.stdout);
  assert.ok(used, p.stderr);
  const lifetimeMs = (Number(used[1]) + Number(used[2])) / 1000;
  const counted = compilerAccounts.get(session.generation)?.countedMs ?? 0;
  assert.ok(counted > 0 && counted <= lifetimeMs + 1, `counted ${counted} ms of a lifetime of ${lifetimeMs} ms`);
  for (const [g, account] of compilerAccounts)
    if (account.lifetimeMs !== null)
      assert.ok(account.countedMs <= account.lifetimeMs + 1, `generation ${g}: ${JSON.stringify(account)}`);
  process.stdout.write(`sessions: the retained compiler's attempts counted ${counted.toFixed(1)} ms of its ` +
    `${lifetimeMs.toFixed(1)} ms\n`);
}

// --- a Node answer of the ledger that changes makes the process
// inconsistent: the attempt fails and the worker is to retire. Last: the
// process stays inconsistent.
{
  useStore();
  // Outside the project, where only Node reads it.
  const target = join(dir, "node-only", "target.js");
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, "export {};\n");
  injectSessionFaultForTests({ kind: "during", during: () => void nodeResolve("./target.js", join(dirname(target), "parent.js")) });
  parse(at(names[0]));
  injectSessionFaultForTests(null);
  assert.ok(retainedLedgerForTests().some((n) => n.node && n.observation[1] === target), "a Node answer in the ledger");
  parse(at(names[3]));
  assert.ok(retainedLedgerForTests().some((n) => n.node && n.observation[1] === target), "kept through a reuse");
  rmSync(target);
  assert.throws(() => parse(at(names[0])), /fresh process is needed/);
  assert.notEqual(processInconsistency(), null, "the worker is to retire");
}
retainDeclarationSessions(false);
process.stdout.write(`sessions: ${requests.length} parses as fresh ones, ${after.reuses - before.reuses} reuses of ` +
  `${after.opens - before.opens} session (${(freshMs / 1000).toFixed(1)} s fresh, ${(reuseMs / 1000).toFixed(1)} s ` +
  `reused); replacements, ledger invalidation, restoration and accounting controls\n`);

