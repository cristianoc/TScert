// The stage store's tests (DESIGN.md, "The stage store"): dependency
// invalidation, concurrent publication by two processes, an interrupted
// writer, a timeout/success race, writable artifact isolation and a longer
// limit executing past a recorded timeout. The stages are shell-script
// stand-ins declared audited for the test, so no build is needed; the
// pipeline's own stages replay in `pipeline/test.mts`.
import assert from "node:assert/strict";
import { spawn, spawnSync, type ChildProcessWithoutNullStreams } from "node:child_process";
import { chmodSync, copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync, readSync, writeFileSync } from "node:fs";
import { platform } from "node:os";
import { join, resolve } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { Store, StoreError, pausePublicationForTests } from "../pipeline/stage-store.mts";
import { auditForTests, canonical, captureCodeIdentity, invokeInProcess, invokeProcess, linkedLibraries, sha256, textCodec, readInvocationLog, Recorder, verifierCall, type Invoked, type ProcessCall }
  from "../pipeline/stages.mts";

const dir = runDirectory("tscert-stage-store-");

/** A stand-in stage program: a shell script, audited with `dependencies`. */
function script(name: string, body: string, dependencies: readonly string[] = ["/bin/cat"]): string {
  const path = join(dir, name);
  writeFileSync(path, `#!/bin/sh\n${body}\n`);
  chmodSync(path, 0o755);
  auditForTests(path, dependencies);
  return path;
}
/** A file of the test's directory holding `text`. */
function file(name: string, text: string): string {
  const path = join(dir, name);
  writeFileSync(path, text);
  return path;
}
/** A lowering by `program` of `input`. */
const lower = (program: string, input: string): ProcessCall => verifierCall(program, ["--lower-control-flow", input]);
/** A search by `program`, its evidence written to `out`. */
const search = (program: string, out: string): ProcessCall =>
  verifierCall(program, ["--produce-source-claims", file("f.json", "fragment"), file("c.json", "claims"), "key", out, "12"]);
const invoke = (call: ProcessCall, limitMs: number = 10_000, force: boolean = false, recorder: Recorder | null = null): Invoked =>
  invokeProcess(call, { limitMs, force, recorder });
/** A fresh store, the one the mechanism uses from now on. */
function freshStore(name: string): Store {
  const root = join(dir, name);
  process.env["TSCERT_STAGE_STORE"] = root;
  return new Store(root);
}

// A real writer held after constructing its entry and before atomic rename.
// stdin releases it; SIGKILL interrupts it without running cleanup.
if (process.argv[2] === "--writer") {
  const [, , , root, kind, attempt] = process.argv;
  const store = new Store(root);
  pausePublicationForTests((directory) => {
    process.stdout.write(directory + "\n");
    readSync(0, Buffer.alloc(1), 0, 1, null);
  });
  const input = "concurrent input", key = sha256(input);
  if (kind === "timeout")
    store.publishTimeout("lower", key, { input, attempt, elapsedMs: 300, limitMs: 300, policy: "test" });
  else
    store.publishFinished("lower", key, { input, exitStatus: 0, stdout: Buffer.from("whole"), stderr: Buffer.alloc(0),
      outputs: [], measurement: { attempt, elapsedMs: 1, limitMs: 1000, cpu: { unavailable: "test" } } });
  process.exit(0);
}

/** A child held at the publication barrier, with its completion observed. */
async function writer(store: Store, kind: string, attempt: string, invocation: readonly string[] = []): Promise<{
  process: ChildProcessWithoutNullStreams; directory: string; closed: Promise<number | null>;
}> {
  const args = invocation.length ? ["--paused-invocation", ...invocation] : ["--writer", store.root, kind, attempt];
  const child = spawn(process.execPath, [import.meta.filename, ...args],
    { env: process.env, timeout: 30_000, killSignal: "SIGKILL" });
  const closed = new Promise<number | null>((done, fail) => {
    child.on("error", fail);
    child.on("close", done);
  });
  const directory = await new Promise<string>((done, fail) => {
    let out = "";
    child.stdout.setEncoding("utf8");
    child.stdout.on("data", (chunk: unknown) => {
      out += String(chunk);
      if (out.includes("\n")) done(out.trim());
    });
    child.on("error", fail);
    child.on("close", () => fail(Error("writer exited before publication barrier")));
  });
  return { process: child, directory, closed };
}

if (process.argv[2] === "--paused-invocation") {
  const [, , , program, input, limit, log] = process.argv;
  auditForTests(program, ["/bin/cat", "/bin/sleep"]);
  pausePublicationForTests((directory) => {
    process.stdout.write(directory + "\n");
    readSync(0, Buffer.alloc(1), 0, 1, null);
  });
  invoke(lower(program, input), Number(limit), true, new Recorder(log));
  process.exit(0);
}
if (process.argv[2] === "--runtime-child") {
  const [, , , program, input] = process.argv;
  auditForTests(program, ["/bin/cat"]);
  process.stdout.write(JSON.stringify(invoke(lower(program, input)).record));
  process.exit(0);
}

// A child process of the concurrency test: one invocation, its record and
// output, or the store error it met, printed as JSON.
if (process.argv[2] === "--child") {
  const [, , , program, input] = process.argv;
  auditForTests(program, ["/bin/cat", "/bin/sleep"]);
  try {
    const result = invoke(lower(program, input));
    process.stdout.write(JSON.stringify({ execution: result.record.execution, stdout: result.stdout }));
  } catch (error) {
    process.stdout.write(JSON.stringify({ error: error instanceof StoreError ? "store" : String(error) }));
  }
  process.exit(0);
}

freshStore("probe");
const probe = invoke(lower(script("probe.sh", '/bin/cat "$2"'), file("probe.json", "probe")));
const eligible = probe.record.key !== null;
if (!eligible) {
  assert.match(probe.record.ineligible ?? "", /macOS only|Node import, require or loader/);
  assert.equal(probe.record.execution, "executed");
  process.stdout.write(`replay ineligible: ${probe.record.ineligible}; invocations execute without keys\n`);
}
const replayExecution = eligible ? "replayed" : "executed";

{
  // Dependency invalidation: the same invocation replays; another input,
  // another program or another declared dependency executes.
  const store = freshStore("invalidation");
  const dependency = file("dependency.txt", "one");
  const program = script("lower.sh", `/bin/cat "$2"; /bin/cat ${dependency}`, ["/bin/cat", dependency]);
  const input = file("input.json", "{}");
  const recorder = new Recorder(join(dir, "invalidation.jsonl"));
  const first = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(first.record.execution, "executed");
  assert.equal(first.record.key !== null, eligible);
  assert.equal(first.stdout, "{}one");
  const again = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(again.record.execution, replayExecution);
  assert.equal(again.record.key, first.record.key);
  assert.equal(again.stdout, "{}one");
  if (eligible) assert.equal(again.record.replay?.stored.attempt, first.record.attempt);
  else assert.equal(again.record.key, null);
  writeFileSync(input, "[]");
  const input2 = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(input2.record.execution, "executed", "another input");
  writeFileSync(dependency, "two");
  const dependency2 = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(dependency2.record.execution, "executed", "another dependency");
  assert.equal(dependency2.stdout, "[]two");
  script("lower.sh", `/bin/cat "$2"; /bin/cat ${dependency}; echo`, ["/bin/cat", dependency]);
  const program2 = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(program2.record.execution, "executed", "another program");
  assert.equal(invoke(lower(program, input), 10_000, true).record.execution, "executed", "forced");
  // An unaudited program executes without a key.
  const unaudited = join(dir, "unaudited.sh");
  writeFileSync(unaudited, `#!/bin/sh\n/bin/cat "$2"\n`);
  chmodSync(unaudited, 0o755);
  const plain = invoke(lower(unaudited, input));
  assert.equal(plain.record.key, null);
  assert.match(plain.record.ineligible ?? "", /not the repository's build of an audited program/);
  assert.equal(invoke(lower(unaudited, input)).record.execution, "executed");
  // The invocation log reads back every attempt in order.
  assert.deepEqual(readInvocationLog(join(dir, "invalidation.jsonl")).map((r) => r.execution),
    ["executed", replayExecution, "executed", "executed", "executed"]);
  if (eligible) assert.ok(readdirSync(join(store.root, "entries", "lower")).length >= 4);
  process.stdout.write("dependency invalidation: eligible identical invocations replay; changed dependencies execute\n");
}

{
  // Writable artifact isolation: each caller receives its own writable copy
  // of a replayed output; changing it changes neither the entry nor another
  // caller's copy.
  freshStore("isolation");
  const program = script("search.sh", `/bin/cat "$2" "$3" > "$5"; echo written`);
  const outputs = ["a", "b", "c"].map((n) => join(dir, `evidence-${n}.json`));
  const first = invoke(search(program, outputs[0]));
  assert.equal(first.record.execution, "executed");
  assert.equal(readFileSync(outputs[0], "utf8"), "fragmentclaims");
  const second = invoke(search(program, outputs[1]));
  assert.equal(second.record.execution, replayExecution);
  assert.equal(readFileSync(outputs[1], "utf8"), "fragmentclaims");
  writeFileSync(outputs[1], "changed by its caller");
  const third = invoke(search(program, outputs[2]));
  assert.equal(third.record.execution, replayExecution);
  assert.equal(readFileSync(outputs[2], "utf8"), "fragmentclaims");
  assert.equal(readFileSync(outputs[0], "utf8"), "fragmentclaims");
  process.stdout.write("artifact isolation: each output is the caller's own writable copy\n");
}

if (eligible) {
  // A timeout is an observation at its limit: reused at that limit or a
  // smaller one; a longer limit executes past it; the finished result it
  // publishes takes precedence over the observation, also over a timeout
  // observed later.
  freshStore("timeouts");
  const program = script("slow.sh", `/bin/sleep 1; /bin/cat "$2"`, ["/bin/cat", "/bin/sleep"]);
  const input = file("slow.json", "slow");
  const timed = invoke(lower(program, input), 300);
  assert.equal(timed.record.execution, "timed-out");
  assert.ok(timed.record.key !== null);
  const reused = invoke(lower(program, input), 300);
  assert.equal(reused.record.execution, "timeout-replayed");
  assert.equal(reused.record.replay?.stored.attempt, timed.record.attempt);
  assert.equal(reused.record.replay?.stored.limitMs, 300);
  assert.equal(invoke(lower(program, input), 200).record.execution, "timeout-replayed", "a smaller limit");
  const longer = invoke(lower(program, input), 5_000);
  assert.equal(longer.record.execution, "executed", "a longer limit executes past the observation");
  assert.equal(longer.stdout, "slow");
  assert.equal(invoke(lower(program, input), 300).record.execution, "replayed", "the finished result first");
  process.stdout.write("timeouts: reused at their limit or below, executed past at a longer one\n");
}

if (eligible) {
  // A corrupt or incomplete entry is a miss; the fresh result is used
  // and not published over it.
  const store = freshStore("interrupted");
  const program = script("lower2.sh", `/bin/cat "$2"`);
  const input = file("interrupted.json", "whole");
  const first = invoke(lower(program, input));
  assert.equal(first.record.execution, "executed");
  assert.ok(first.record.key !== null);
  const entry = join(store.root, "entries", "lower", first.record.key);
  chmodSync(join(entry, "stdout"), 0o644);
  writeFileSync(join(entry, "stdout"), "torn");
  const torn = invoke(lower(program, input));
  assert.equal(torn.record.execution, "executed", "a corrupt entry is a miss");
  assert.equal(torn.stdout, "whole");
  assert.equal(readFileSync(join(entry, "stdout"), "utf8"), "torn", "an invalid entry is not replaced");
  chmodSync(join(entry, "manifest.json"), 0o644);
  writeFileSync(join(entry, "manifest.json"), "{");
  assert.equal(invoke(lower(program, input)).record.execution, "executed", "an incomplete manifest is a miss");
  store.clean();
  assert.equal(invoke(lower(program, input)).record.execution, "executed");
  assert.equal(invoke(lower(program, input)).record.execution, "replayed");
  process.stdout.write("corrupt entries: a corrupt or incomplete entry is a miss\n");
}

if (eligible) {
  // Concurrent publication by two processes: both execute, one publishes,
  // the other finds the same result present; a stage giving two results for
  // one key is a store error.
  const child = (program: string, input: string): Promise<string> => new Promise((done, fail) => {
    const p = spawn(process.execPath, [import.meta.filename, "--child", program, input], { env: process.env });
    let out = "";
    p.stdout.setEncoding("utf8");
    p.stdout.on("data", (text: unknown) => { out += String(text); });
    p.on("error", fail);
    p.on("close", () => done(out));
  });
  const parsed = (text: string): unknown => JSON.parse(text);
  const store = freshStore("concurrent");
  const steady = script("steady.sh", `/bin/sleep 1; /bin/cat "$2"`, ["/bin/cat", "/bin/sleep"]);
  const input = file("concurrent.json", "same");
  const both = await Promise.all([child(steady, input), child(steady, input)]);
  for (const out of both) assert.deepEqual(parsed(out), { execution: "executed", stdout: "same" });
  assert.equal(readdirSync(join(store.root, "entries", "lower")).length, 1);
  assert.equal(invoke(lower(steady, input)).record.execution, "replayed");
  const varying = script("varying.sh", `/bin/sleep 1; echo $$`, ["/bin/sleep"]);
  const outcomes = (await Promise.all([child(varying, input), child(varying, input)])).map(parsed);
  assert.equal(outcomes.filter((o) => typeof o === "object" && o !== null && "error" in o && o.error === "store").length, 1, JSON.stringify(outcomes));
  process.stdout.write("concurrent publication: one entry for two writers; two results for one key a store error\n");
}


{
  const store = freshStore("killed-writer");
  const held = await writer(store, "finished", "interrupted");
  assert.ok(existsSync(join(held.directory, "manifest.json")), "entry complete before rename");
  assert.equal(store.finished("lower", sha256("concurrent input"), "concurrent input"), null);
  store.clean();
  assert.ok(existsSync(held.directory), "cleanup spares the live writer");
  held.process.kill("SIGKILL");
  await held.closed;
  assert.equal(store.finished("lower", sha256("concurrent input"), "concurrent input"), null);
  const next = await writer(store, "finished", "next");
  next.process.stdin.end();
  assert.equal(await next.closed, 0);
  assert.equal(store.finished("lower", sha256("concurrent input"), "concurrent input")?.result.stdout.toString(), "whole");
  store.clean();
  assert.equal(existsSync(held.directory), false, "cleanup removes the dead writer");
  process.stdout.write("interrupted publication: real writer killed before rename; reader misses, fresh writer publishes, cleanup removes abandoned entry\n");
}
for (const order of [["timeout", "finished"], ["finished", "timeout"]]) {
  const store = freshStore("race-" + order.join("-"));
  const timeout = await writer(store, "timeout", "timeout");
  const finished = await writer(store, "finished", "finished");
  for (const kind of order) {
    const held = kind === "timeout" ? timeout : finished;
    held.process.stdin.end();
    assert.equal(await held.closed, 0);
  }
  assert.ok(store.timeout("lower", sha256("concurrent input"), "concurrent input", 300, "test"));
  assert.equal(store.finished("lower", sha256("concurrent input"), "concurrent input")?.result.stdout.toString(), "whole");
  process.stdout.write(`concurrent publication ${order.join(" then ")}: later reader gets finished result\n`);
}
{
  const log = file("interrupted-log.jsonl", "");
  const recorder = new Recorder(log);
  const original = probe.record;
  recorder.start({ ...original, execution: "interrupted" }, Date.now() - 1000);
  const [interrupted] = readInvocationLog(log);
  assert.deepEqual(interrupted.manifest, original.manifest);
  assert.equal(interrupted.limitMs, original.limitMs);
  assert.equal(interrupted.ineligible, original.ineligible);
  assert.ok(interrupted.elapsedMs >= 1000);
  assert.equal(interrupted.execution, "interrupted");
}
{
  freshStore("loaded-code");
  const module = file("loaded.mts", "export const value: string = 'old';");
  const implementation = captureCodeIdentity([module]);
  const call = { stage: "assemble", implementation, inputs: [], codec: textCodec, run: (): string => "old" };
  const invokeLoaded = (): ReturnType<typeof invokeInProcess<string>> =>
    invokeInProcess({ ...call, stage: "assemble" }, { force: false, recorder: null });
  invokeLoaded();
  writeFileSync(module, "export const value: string = 'new';");
  const stale = invokeLoaded();
  assert.equal(stale.value, "old");
  assert.equal(stale.record.key, null);
  assert.match(stale.record.ineligible ?? "", /loaded implementation/);
  assert.equal(stale.record.execution, "executed");
}

if (eligible) {
  const store = freshStore("interrupted-invocation");
  const program = script("pause.sh", '/bin/cat "$2"', ["/bin/cat", "/bin/sleep"]);
  const input = file("pause.json", "whole"), log = file("pause.jsonl", "");
  const held = await writer(store, "", "", [program, input, "10000", log]);
  assert.ok(existsSync(join(held.directory, "manifest.json")));
  held.process.kill("SIGKILL");
  await held.closed;
  const [interrupted] = readInvocationLog(log);
  assert.equal(interrupted.execution, "interrupted");
  assert.equal(interrupted.limitMs, 10000);
  assert.ok(interrupted.manifest !== null);
  assert.ok(interrupted.elapsedMs > 0);
  assert.equal(invoke(lower(program, input)).record.execution, "executed", "dead writer never published");
  assert.equal(invoke(lower(program, input)).record.execution, "replayed");
  store.clean();
  assert.equal(existsSync(held.directory), false);
}
if (eligible) for (const order of [["timeout", "finished"], ["finished", "timeout"]]) {
  const store = freshStore("invocation-race-" + order.join("-"));
  const program = script("race.sh", '/bin/sleep 1; /bin/cat "$2"', ["/bin/cat", "/bin/sleep"]);
  const input = file("race.json", "whole");
  const timeoutLog = file("race-timeout.jsonl", ""), finishedLog = file("race-finished.jsonl", "");
  const [timeout, finished] = await Promise.all([
    writer(store, "", "", [program, input, "300", timeoutLog]),
    writer(store, "", "", [program, input, "10000", finishedLog]),
  ]);
  for (const kind of order) {
    const held = kind === "timeout" ? timeout : finished;
    held.process.stdin.end();
    assert.equal(await held.closed, 0);
  }
  const [timed] = readInvocationLog(timeoutLog), [done] = readInvocationLog(finishedLog);
  assert.equal(timed.execution, "timed-out");
  assert.equal(done.execution, "executed");
  assert.equal(timed.key, done.key);
  const later = invoke(lower(program, input), 300);
  assert.equal(later.record.execution, "replayed");
  assert.equal(later.stdout, "whole");
  process.stdout.write(`actual invocation race ${order.join(" then ")}: finished result replays\n`);
}
if (platform() === "darwin") {
  // Minimal Mach-O load commands let otool traverse a real dependency graph
  // without compiling or executing a fixture.
  const macho = (path: string, dependencies: readonly string[]): void => {
    const commands = dependencies.map((dependency) => {
      const name = Buffer.from(dependency + "\0");
      const command = Buffer.alloc(Math.ceil((24 + name.length) / 8) * 8);
      command.writeUInt32LE(12, 0); // LC_LOAD_DYLIB
      command.writeUInt32LE(command.length, 4);
      command.writeUInt32LE(24, 8);
      name.copy(command, 24);
      return command;
    });
    const header = Buffer.alloc(32);
    header.writeUInt32LE(0xfeedfacf, 0);
    header.writeUInt32LE(0x0100000c, 4);
    header.writeUInt32LE(6, 12); // MH_DYLIB
    header.writeUInt32LE(commands.length, 16);
    header.writeUInt32LE(commands.reduce((n, c) => n + c.length, 0), 20);
    writeFileSync(path, Buffer.concat([header, ...commands]));
  };
  const executable = join(dir, "closure"), library = join(dir, "library"), other = join(dir, "other");
  macho(other, []);
  macho(library, []);
  macho(executable, [library]);
  const first = linkedLibraries(executable);
  assert.ok(typeof first !== "string", String(first));
  macho(library, [other]);
  const changed = linkedLibraries(executable);
  assert.notEqual(canonical(changed), canonical(first), "linked library replacement invalidates identity");
  macho(executable, [other]);
  const relinked = linkedLibraries(executable);
  assert.notEqual(canonical(relinked), canonical(changed), "relink follows current dependency closure");
}
{
  const copied = join(dir, "loaded-copy");
  mkdirSync(copied);
  for (const name of ["claims-assembly.mts", "stages.mts", "stage-store.mts", "run-directory.mts"])
    copyFileSync(resolve(import.meta.dirname, "../pipeline", name), join(copied, name));
  const driver = join(copied, "test.mts");
  writeFileSync(driver, String.raw`
import assert from "node:assert/strict";
import { appendFileSync } from "node:fs";
import { assembleClaims, assemblyImplementation } from "./claims-assembly.mts";
import { invokeInProcess, textCodec } from "./stages.mts";
const run = (): ReturnType<typeof invokeInProcess<string>> => invokeInProcess({
  stage: "assemble", implementation: assemblyImplementation, inputs: [], codec: textCodec,
  run: (): string => assembleClaims('{"modules":[]}', [])
}, { force: false, recorder: null });
run();
appendFileSync(new URL(process.argv[2], import.meta.url), "\n// edited during worker lifetime\n");
const result = run();
assert.equal(result.value, '{"modules":[]}');
assert.equal(result.record.execution, "executed");
assert.equal(result.record.key, null);
assert.match(result.record.ineligible ?? "", /loaded .*modules differ from disk/);
`);
  for (const name of ["claims-assembly.mts", "stages.mts"]) {
    const child = spawnSync(process.execPath, [driver, "./" + name], { encoding: "utf8", env: process.env });
    assert.equal(child.status, 0, child.stderr);
  }
  const program = script("runtime.sh", '/bin/cat "$2"');
  const input = file("runtime.json", "runtime"), preload = file("preload.mjs", "");
  for (const args of [["--import", preload], ["--require", preload], ["--experimental-loader", preload], ["--experimental_loader", preload], ["-r", preload]]) {
    const child = spawnSync(process.execPath, [...args, import.meta.filename, "--runtime-child", program, input],
      { encoding: "utf8", env: process.env });
    assert.equal(child.status, 0, child.stderr);
    const [record] = readInvocationLog(file("runtime-log.jsonl", JSON.stringify({ event: "end", record: JSON.parse(child.stdout) }) + "\n"));
    assert.equal(record.key, null);
    assert.equal(record.execution, "executed");
    assert.match(record.ineligible ?? "", /Node import, require or loader/);
  }
  const child = spawnSync(process.execPath, [import.meta.filename, "--runtime-child", program, input],
    { encoding: "utf8", env: { ...process.env, NODE_OPTIONS: `--import="${preload}"` } });
  assert.equal(child.status, 0, child.stderr);
  assert.match(child.stdout, /Node import, require or loader/);
  process.stdout.write("loaded code and Node preload options: changed or unidentified dependencies execute without a key\n");
}
{
  const store = freshStore("snapshot-cleanup");
  const files: [string, Buffer][] = [["source.ts", Buffer.from("export const value = 1;\n")]];
  const snapshot = store.stableDirectory("sources", files);
  assert.ok(snapshot);
  store.clean();
  assert.equal(readFileSync(join(snapshot, "source.ts"), "utf8"), files[0][1].toString());
  assert.equal(store.stableDirectory("sources", files), snapshot);
  process.stdout.write("cleanup preserves validated source snapshots for active readers\n");
}
assert.throws(() => invoke(lower(script("any.sh", "/bin/cat \"$2\""), file("x.json", "x")), 0), /positive integer/);
process.stdout.write("limits: a stage's limit is a positive integer number of milliseconds\n");
