// The controls of retained declaration sessions (STAGE-STORE.md, "Retained
// declaration sessions"), each through the production stage adapters
// (`parseCall`, `diagnosticsCall`, `invokeInProcess`) over a private copy of
// the value-import examples and their named project:
// - a parse in a reused session, its work shared, is byte for byte the parse in fresh
//   compilers with no work shared at the same paths, refusals as well as successes, in forward,
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
import { compilerAccounts, failCompilerReadingsForTests, invokeInProcess, Recorder, type AttemptRecord } from "../pipeline/stages.mts";
import { Store } from "../pipeline/stage-store.mts";
import { diagnosticsCall, parseCall, type Parsed } from "../pipeline/parse-stage.mts";
import { runnerBuild } from "../pipeline/stage-execution.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";
import { compilerApiFamily } from "../tools/compiler-api.mts";
import { useFamiliesForTests } from "../tools/family-activation.mts";
import { parserOpenings } from "../tools/fragment-parse.mts";
import { nodeResolve, observed, processInconsistency, processRetirement, sharingForTests, unobservable } from "../tools/files.mts";
import { compilerImplementation } from "../tools/compiler-channel.mts";
import { textCodec } from "../pipeline/in-process-execution.mts";
import { clientErrors } from "../tools/declaration-graph.mts";
import { liveCompilers } from "../tools/compiler-processes.mts";
import { asideForTests, declarationSessionTelemetry, injectSessionFaultForTests, retainDeclarationSessions, retainedDeclarationSession,
  inDeclarationAttempt, retainedLedgerForTests } from "../tools/declaration-session.mts";
import type { SeenDiagnostic } from "../tools/declaration-graph.mts";

const here = import.meta.dirname;
const repository = resolve(here, "..");
const dir = runDirectory("tscert-sessions-");

const extras = ["computed-conditional", "written-instantiated-bounds", "shadowing", "shadowed-locals"];
/** A copy of the value-import examples beside the modules they import, in
 * one project directory, at `name`. */
function fixture(name: string): { examples: string; config: string } {
  const project = join(dir, name);
  cpSync(join(repository, "pipeline", "imports-project"), project, { recursive: true });
  for (const file of readdirSync(join(repository, "pipeline", "examples")).filter((f) => f.includes("value-import") && f.endsWith(".ts")))
    cpSync(join(repository, "pipeline", "examples", file), join(project, file));
  // Probes of computed forms, and shadowing locals.
  for (const name of extras) cpSync(join(repository, "pipeline", "examples", `${name}.ts`), join(project, `extra-${name}.ts`));
  // A module with TypeScript errors, for diagnostics; a configuration only a
  // compiler request reads.
  writeFileSync(join(project, "extra-errors.ts"),
    "export const a: number = \"one\";\nexport function f(x: string): number {\n  return x;\n}\n");
  writeFileSync(join(project, "lazy.json"), JSON.stringify({ compilerOptions: { strict: true } }));
  const config = join(project, "tsconfig.json");
  writeFileSync(config, readFileSync(config, "utf8").replace('"../examples/*value-import*.ts"', '"./*value-import*.ts", "./extra-*.ts"')
    .replace('"../../tools/resolvable.d.ts"', JSON.stringify(join(repository, "tools", "resolvable.d.ts"))));
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
function parse(r: Request, force: boolean = true, recorder: Recorder = new Recorder(null)): Parse {
  const s = snapshot(r.examples, r.name, r.directory);
  return invokeInProcess(parseCall(s.bytes, s.file, r.config, r.config ? s.resolution : s.file),
    { force, recorder });
}
/** The parse of `r` in fresh compilers, no work shared: no session retained, no answer kept (STAGE-STORE.md, "Shared work"). */
function fresh(r: Request): Parsed {
  return asideForTests(() => sharingForTests(false, () => parse(r).value));
}
const telemetry = declarationSessionTelemetry;
const generation = (): number | null => retainedDeclarationSession()?.generation ?? null;
/** The retained session's base state: its one project, no document, no overlay. */
function clean(config: string, what: string): void {
  const s = retainedDeclarationSession();
  assert.ok(s, `${what}: a session is retained`);
  assert.deepEqual(s.projects, [config], what);
  assert.equal(s.documents, 0, what);
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
  "invalid-written-whole-class-value-import", "written-pick-value-import", "written-helper-global-value-import",
  ...extras.map((n) => `extra-${n}`)];

// A process of its own for the incomplete Node read (below).
if (process.argv[2] === "--node-incomplete") {
  const directory = join(dir, "node-incomplete");
  mkdirSync(join(directory, "node_modules", "plain"), { recursive: true });
  writeFileSync(join(directory, "node_modules", "plain", "package.json"), JSON.stringify({ name: "plain", main: "index.js" }));
  writeFileSync(join(directory, "node_modules", "plain", "index.js"), "export {};\n");
  parse(at(names[0]));
  injectSessionFaultForTests({ kind: "during", during: () => void nodeResolve("plain", join(directory, "main.js")) });
  const done = parse(at(names[3]));
  injectSessionFaultForTests(null);
  assert.equal(done.record.key, null);
  assert.match(done.record.ineligible ?? "", /states no exports/);
  assert.equal(retainedDeclarationSession(), null, "the session is not retained");
  assert.match(processRetirement() ?? "", /states no exports/);
  assert.throws(() => parse(at(names[0])), /fresh process is needed/);
  process.stdout.write("retired\n");
  process.exit(0);
}
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
assert.ok(after.probes > before.probes, "reused sessions made probe programs");
assert.equal(after.opens - before.opens, 1, "one declaration compiler opened");
assert.ok(after.reuses - before.reuses >= requests.length - 1, "every later collection reuses it");
assert.equal(after.replacements, before.replacements);
assert.ok(parserOpenings() - parsersBefore >= requests.length);

// --- TypeScript's diagnostics between parses reuse the session, clean
// before and after; the same as in a fresh compiler
for (const name of [names[0], "extra-errors"]) {
  const file = join(base.examples, `${name}.ts`);
  const call = (): SeenDiagnostic[] => invokeInProcess(diagnosticsCall(file, base.config),
    { force: true, recorder: null }).value;
  const reference = asideForTests(call);
  if (name === "extra-errors") assert.ok(reference.length >= 2, "two TypeScript errors, in order");
  parse(at(names[1]));
  clean(base.config, "before diagnostics");
  const was = telemetry(), session = generation();
  assert.deepEqual(call(), reference, `${name}: diagnostics`);
  clean(base.config, "after diagnostics");
  assert.equal(generation(), session, "diagnostics reuse the session");
  assert.equal(telemetry().opens, was.opens);
  assert.equal(telemetry().reuses, was.reuses + 1);
  const again = name === "extra-errors" ? names[3] : name;
  assert.deepEqual(parse(at(again)).value, references.get(key(at(again))), `${again} after diagnostics`);
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
  replaces("a changed dependency", () => {
    const changed = same(r(names[1]), "after the dependency changed");
    assert.notDeepEqual(changed.value, dependent.value, "the dependency's real path is in the Fragment");
  });
  assert.match(telemetry().lastReplacement ?? "", new RegExp(`real ${d}`));
  process.env["TSCERT_STAGE_STORE"] = storeOne;
  assert.equal(parse(r(names[1]), false).record.execution, "executed", "the entry no longer replays");

  // A probe's collection makes observations the session had not made.
  const probing = "written-pick-value-import";
  const beforeProbe = ledger();
  const probed = parse(r(probing));
  const firstByProbe = [...ledger().keys()].filter((k) => !beforeProbe.has(k) && !k.startsWith("real "));
  assert.ok(firstByProbe.length > 0, "a probe's collection reads what the session had not");
  for (const k of firstByProbe) assert.ok(observationsOf(storeOne, probed.record).includes(k), `${k} in the probe's entry`);

  // A file a later compiler request reads first: in the ledger and the entry;
  // its change replaces the session and refuses the entry.
  const lazy = join(later.examples, "lazy.json");
  assert.ok(!ledger().has(`read ${lazy}`), "not read before");
  injectSessionFaultForTests({ kind: "during", during: (compilerRead) => compilerRead(lazy) });
  const reading = parse(r(names[3]));
  injectSessionFaultForTests(null);
  assert.ok(ledger().has(`read ${lazy}`), "the compiler's read is in the ledger");
  assert.ok(observationsOf(storeOne, reading.record).includes(`read ${lazy}`), "and in the entry");
  writeFileSync(lazy, JSON.stringify({ compilerOptions: { strict: false } }));
  useStore();
  replaces("a changed file a compiler request read", () => void same(r(names[3]), "after the requested file changed"));
  assert.match(telemetry().lastReplacement ?? "", /lazy\.json/);
  process.env["TSCERT_STAGE_STORE"] = storeOne;
  assert.equal(parse(r(names[3]), false).record.execution, "executed", "its entry no longer replays");
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
released("a document requested", { kind: "document-request", document: join(base.examples, "lib.ts") },
  /restoration failed: a declaration session opens no document/);
{
  const outside = join(dir, "outside", "document.ts");
  mkdirSync(dirname(outside), { recursive: true });
  writeFileSync(outside, "export const x = 1;\n");
  released("a document outside the project left open", { kind: "document-left", document: outside },
    /restoration failed: the session holds the projects/);
}
released("a document of the project left open", { kind: "document-left", document: join(base.examples, "lib.ts") },
  /restoration failed: the session holds the open documents/);

// --- a record begun during a reused collection holds the session's ledger:
// what it computes may read the compiler the ledger's answers determine
{
  parse(at(names[0]));
  const nested: { observations: readonly (readonly [string, string, string | null])[] }[] = [];
  injectSessionFaultForTests({ kind: "during", during: () => void nested.push(observed(() => 0)) });
  parse(at(names[3]));
  injectSessionFaultForTests(null);
  const [made] = nested;
  assert.ok(made, "the nested record was made");
  assert.ok(made.observations.some(([operation, path]) => operation === "read" && path === base.config),
    "a nested record holds the ledger's read of the configuration");
}

// --- at an attempt's end, the ledger of a session the attempt used and
// released is checked too: a change to what only it read publishes nothing
{
  useStore();
  const first = fixture("evicted-a"), second = fixture("evicted-b");
  const touch = (): void => writeFileSync(join(first.examples, "lib.ts"), readFileSync(join(first.examples, "lib.ts"), "utf8") + "\n");
  // The second session's collection runs in the attempt itself, or in a
  // nested stage, whose own end checks only what it used.
  const attempt = (mutate: boolean, nested: boolean): AttemptRecord => invokeInProcess({ stage: "diagnostics",
    inputs: [{ role: "control", bytes: `evicted ${mutate} ${nested}` }], observed: { compiler: compilerImplementation },
    codec: textCodec, run: (): string => inDeclarationAttempt(() => {
      const one = clientErrors(join(first.examples, `${names[0]}.ts`), first.config);
      const file = join(second.examples, `${names[0]}.ts`);
      const two = nested ? invokeInProcess(diagnosticsCall(file, second.config), { force: true, recorder: null }).value
        : clientErrors(file, second.config);
      if (mutate) touch();
      return JSON.stringify([one, two]);
    }) }, { force: true, recorder: null }).record;
  for (const nested of [false, true]) {
    assert.notEqual(attempt(false, nested).key, null, `nested ${nested}: an attempt over two sessions, nothing changed, is published`);
    const changed = attempt(true, nested);
    assert.equal(changed.key, null, `nested ${nested}: a change to the released session's dependency publishes nothing`);
    assert.match(changed.ineligible ?? "", /ledger does not hold at the attempt's end: read .*lib\.ts/);
  }
}

// --- nested attempts each count their own time: an observed attempt around
// a parse and around a non-observed attempt using a session; together they
// count what the process and the compilers used
{
  parse(at(names[0]));
  const session = liveCompilers().at(-1);
  assert.ok(session);
  const reading = (): number => {
    const p = spawnSync(runnerBuild, ["--cpu", String(session.pid)], { encoding: "utf8" });
    const used = /^cpu (\d+) (\d+) (\d+)\n$/.exec(p.stdout);
    assert.ok(used, p.stderr);
    return (Number(used[1]) + Number(used[2])) / 1000;
  };
  const ms = (cpu: AttemptRecord["cpu"]): number => {
    assert.ok("userMs" in cpu, JSON.stringify(cpu));
    return cpu.userMs + cpu.systemMs;
  };
  const ended = new Set(compilerAccounts.keys());
  const node0 = process.cpuUsage(), session0 = reading();
  const records: AttemptRecord[] = [];
  const plainMs: number[] = [];
  const outer = invokeInProcess({ stage: "diagnostics", inputs: [{ role: "control", bytes: "nested cpu" }],
    observed: { compiler: compilerImplementation }, codec: textCodec, run: (): string => {
      // The parse and the stages nested in it, each attempt's time its own.
      const nested = new Recorder(null);
      parse(at(names[3]), true, nested);
      records.push(...nested.records);
      // Read independently around the non-observed attempt: its own time.
      const plainNode = process.cpuUsage(), plainSession = reading();
      records.push(invokeInProcess({ stage: "assemble", inputs: [{ role: "control", bytes: "plain" }], codec: textCodec,
        run: (): string => JSON.stringify(clientErrors(join(base.examples, `${names[0]}.ts`), base.config)) },
        { force: true, recorder: null }).record);
      const used = process.cpuUsage(plainNode);
      plainMs.push((used.user + used.system) / 1000 + reading() - plainSession);
      return "";
    } }, { force: true, recorder: null }).record;
  const node = process.cpuUsage(node0);
  const total = (node.user + node.system) / 1000 + reading() - session0 +
    [...compilerAccounts].filter(([g, a]) => !ended.has(g) && a.lifetimeMs !== null).reduce((sum, [, a]) => sum + (a.lifetimeMs ?? 0), 0);
  const counted = ms(outer.cpu) + records.reduce((sum, r) => sum + ms(r.cpu), 0);
  assert.ok(Math.abs(total - counted) <= Math.max(30, total / 10), `nested attempts counted ${counted} ms of ${total} ms`);
  assert.ok(records.every((r) => ms(r.cpu) > 0) && ms(outer.cpu) < counted, "each attempt counts its own time");
  // The non-observed attempt's record holds the compiler time it caused.
  const plain = ms(records.at(-1)?.cpu ?? outer.cpu), around = plainMs[0] ?? 0;
  assert.ok(plain <= around + 1 && around - plain <= Math.max(15, around / 10),
    `the non-observed attempt counted ${plain} ms of the ${around} ms read around it`);
  process.stdout.write(`sessions: nested attempts counted ${counted.toFixed(1)} ms (outer ${ms(outer.cpu).toFixed(1)} ms) ` +
    `of the ${total.toFixed(1)} ms the process and the compilers used\n`);
  // A reading not taken makes the attempt's CPU time unavailable.
  failCompilerReadingsForTests(1);
  const unread = parse(at(names[0])).record;
  failCompilerReadingsForTests(0);
  assert.ok("unavailable" in unread.cpu && /not read/.test(unread.cpu.unavailable), JSON.stringify(unread.cpu));
}

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
  // The attempts count all but the time the compiler used idle between them.
  const close = (countedMs: number, lifetime: number): boolean =>
    countedMs <= lifetime + 1 && lifetime - countedMs <= Math.max(20, lifetime / 10);
  assert.ok(counted > 0 && close(counted, lifetimeMs), `counted ${counted} ms of a lifetime of ${lifetimeMs} ms`);
  let ended = 0;
  for (const [g, account] of compilerAccounts)
    if (account.lifetimeMs !== null) {
      ended++;
      assert.ok(close(account.countedMs, account.lifetimeMs), `generation ${g}: ${JSON.stringify(account)}`);
    }
  assert.ok(ended > 10, "compilers replaced, discarded and fresh ones ended during attempts");
  process.stdout.write(`sessions: the retained compiler's attempts counted ${counted.toFixed(1)} ms of its ` +
    `${lifetimeMs.toFixed(1)} ms\n`);
}

// --- an incomplete Node read during a collection: the attempt publishes
// nothing, the session is not retained, and the process executes no further
// observed stage: it is to retire (in a process of its own)
{
  const child = spawnSync(process.execPath, [import.meta.filename, "--node-incomplete"], { encoding: "utf8" });
  assert.equal(child.status, 0, child.stderr);
  assert.match(child.stdout, /retired/);
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

