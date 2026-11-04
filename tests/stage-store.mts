// The stage store's tests (DESIGN.md, "The stage store"): streams larger
// than a pipe's buffer executed and replayed, dependency invalidation, concurrent publication by two processes, an interrupted
// writer, a timeout/success race, writable artifact isolation, a longer
// limit executing past a recorded timeout and a retry of timeouts executing
// it again at the same limit, an edit of the replay policy, which no key
// covers, replaying its entries, and eviction within a budget. The stages are shell-script
// stand-ins declared audited for the test, so no build is needed; the
// pipeline's own stages replay in `pipeline/test.mts`.
import assert from "node:assert/strict";
import { spawn, spawnSync, type ChildProcessWithoutNullStreams } from "node:child_process";
import { chmodSync, closeSync, copyFileSync, existsSync, lstatSync, mkdirSync, openSync, readdirSync, readFileSync, readSync, rmSync,
  symlinkSync, utimesSync, writeFileSync } from "node:fs";
import { randomUUID } from "node:crypto";
import { hostname, platform } from "node:os";
import { basename, join, resolve } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { Store, StoreError, pausePublicationForTests, pauseLockForTests } from "../pipeline/stage-store.mts";
import { invokeProcess, readInvocationLog, Recorder, startEviction, type Invoked } from "../pipeline/stages.mts";
import { auditForTests, canonical, linkedLibraries, runnerBuild, sha256, verifierCall, type ProcessCall }
  from "../pipeline/stage-execution.mts";

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
  verifierCall(program, ["--produce-units", file("f.json", "fragment"), file("c.json", "claims"), "key", out, "12"]);
const invoke = (call: ProcessCall, limitMs: number = 10_000, force: boolean = false, recorder: Recorder | null = null): Invoked =>
  invokeProcess(call, { limitMs, force, recorder });
/** A fresh store, the one the mechanism uses from now on. */
function freshStore(name: string): Store {
  return use(new Store(join(dir, name)));
}
/** `store`, the one the mechanism uses from now on: a section running
 * beside others names its store again before each invocation it makes. */
function use(store: Store): Store {
  process.env["TSCERT_STAGE_STORE"] = store.root;
  return store;
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
    store.publishTimeout("lower", key, { input, attempt, elapsedMs: 300, limitMs: 300, policy: "test",
      cpu: { unavailable: "test" } });
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
    { env: { ...process.env, TSCERT_STAGE_STORE: store.root }, timeout: 30_000, killSignal: "SIGKILL" });
  const started = Date.now();
  let errors = "";
  child.stderr.setEncoding("utf8");
  child.stderr.on("data", (chunk: unknown) => {
    errors += String(chunk);
  });
  const closed = new Promise<number | null>((done, fail) => {
    child.on("error", fail);
    child.on("close", (code: number | null, signal: NodeJS.Signals | null) => {
      // A writer ended by a signal, a test's own kill or another, says which and when.
      if (code === null)
        process.stderr.write(`writer ${args.join(" ")} ended by ${String(signal)} after ${Date.now() - started} ms${
          errors ? `; its standard error: ${errors.trim().slice(0, 2000)}` : ""}\n`);
      done(code);
    });
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

// A child process of the eviction controls: one operation on the store at
// `root`, by a process that has stopped once a pass runs.
if (process.argv[2] === "--store-op") {
  const [, , , root, op, ...rest] = process.argv;
  const store = new Store(root);
  if (op === "publish")
    for (const input of rest) evictable(store, "lower", input);
  else if (op === "replay")
    for (const input of rest) assert.ok(store.finished("lower", sha256(input), input), `replay of ${input}`);
  else if (op === "observed") {
    const preKey = sha256(`pre ${rest[0]}`);
    evictable(store, "parse", rest[0]);
    store.reference("parse", preKey, sha256(rest[0]));
  } else if (op === "timeouts") {
    const [input, ...attempts] = rest;
    for (const attempt of attempts)
      store.publishTimeout("lower", sha256(input), { input, attempt, elapsedMs: 300, limitMs: 300, policy: "test",
        cpu: { unavailable: "test" } });
  } else if (op === "snapshot") {
    const snapshot = store.stableDirectory("sources", [["source.ts", Buffer.from(rest[0])]]);
    process.stdout.write(`${snapshot}\n`);
  } else if (op === "read") {
    // Replays of one entry until the file `rest[1]` exists or the test that
    // started it has stopped, while another process publishes and evicts
    // it: each is the entry's own result or a miss.
    const input = rest[0], stop = rest[1], parent = process.ppid;
    const counts = { hits: 0, misses: 0, wrong: 0 };
    process.stdout.write("ready\n");
    while (!existsSync(stop) && process.ppid === parent) {
      const found = store.finished("lower", sha256(input), input);
      if (!found) counts.misses++;
      else if (found.result.stdout.equals(evictableOutput(input))) counts.hits++;
      else counts.wrong++;
    }
    process.stdout.write(JSON.stringify(counts) + "\n");
  }
  process.exit(0);
}

/** The output an eviction control's entry for `input` holds: 5000 bytes. */
function evictableOutput(input: string): Buffer {
  return Buffer.alloc(5000, input);
}
/** Publish an eviction control's entry for `input` at `stage`. */
function evictable(store: Store, stage: string, input: string): void {
  store.publishFinished(stage, sha256(input), { input, exitStatus: 0, stdout: evictableOutput(input), stderr: Buffer.alloc(0),
    outputs: [], measurement: { attempt: randomUUID(), elapsedMs: 1, limitMs: 1000, cpu: { unavailable: "test" } } });
}
/** One operation on `store` by a child process, which stops once it is done;
 * its output. */
function storeOp(store: Store, op: string, ...args: string[]): string {
  const child = spawnSync(process.execPath, [import.meta.filename, "--store-op", store.root, op, ...args], { encoding: "utf8" });
  assert.equal(child.status, 0, child.stderr);
  return child.stdout;
}
/** The process number of a process that has stopped. */
function stoppedPid(): number {
  const child = spawnSync(process.execPath, ["-e", "0"]);
  assert.equal(child.status, 0);
  return child.pid ?? 0;
}
/** The bytes the files below `parts` take, in whole 4 KiB blocks. */
function onDisk(...parts: string[]): number {
  const path = join(...parts);
  const s = lstatSync(path);
  if (!s.isDirectory()) return Math.ceil(s.size / 4096) * 4096;
  return readdirSync(path).reduce((sum, name) => sum + onDisk(path, name), 0);
}

freshStore("probe");
const probe = invoke(lower(script("probe.sh", '/bin/cat "$2"'), file("probe.json", "probe")));
const eligible = probe.record.key !== null;
if (!eligible) {
  assert.match(probe.record.ineligible ?? "", /macOS and Linux only|Node import, require or loader|Node DYLD_|Node LD_|ld\.so\.preload/);
  assert.equal(probe.record.execution, "executed");
  process.stdout.write(`replay ineligible: ${probe.record.ineligible}; invocations execute without keys\n`);
}
const replayExecution = eligible ? "replayed" : "executed";

{
  freshStore("dyld-runtime");
  const program = script("dyld.sh", '/bin/cat "$2"');
  const input = file("dyld.json", "runtime");
  for (const name of ["DYLD_LIBRARY_PATH", "DYLD_INSERT_LIBRARIES", "DYLD_FRAMEWORK_PATH", "DYLD_TEST_OVERRIDE"]) {
    for (let attempt = 0; attempt < 2; attempt++) {
      const child = spawnSync(process.execPath, [import.meta.filename, "--runtime-child", program, input],
        { encoding: "utf8", env: { ...process.env, [name]: "" } });
      assert.equal(child.status, 0, child.stderr);
      const [record] = readInvocationLog(file("dyld-log.jsonl",
        JSON.stringify({ event: "end", record: JSON.parse(child.stdout) }) + "\n"));
      assert.equal(record.key, null);
      assert.equal(record.execution, "executed");
      assert.match(record.ineligible ?? "", eligible ? /Node DYLD_/ : /macOS and Linux only|Node DYLD_/);
      const result = invoke({ ...lower(program, input), environment: { [name]: "" } });
      assert.equal(result.record.key, null);
      assert.equal(result.record.execution, "executed");
      assert.match(result.record.ineligible ?? "", eligible ? /child DYLD_/ : /macOS and Linux only|child DYLD_/);
    }
  }
  for (const name of ["LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT"]) {
    const child = spawnSync(process.execPath, [import.meta.filename, "--runtime-child", program, input],
      { encoding: "utf8", env: { ...process.env, [name]: "" } });
    assert.equal(child.status, 0, child.stderr);
    const [record] = readInvocationLog(file("ld-log.jsonl",
      JSON.stringify({ event: "end", record: JSON.parse(child.stdout) }) + "\n"));
    assert.equal(record.key, null);
    assert.match(record.ineligible ?? "", eligible ? /Node LD_/ : /macOS and Linux only|Node LD_/);
    const result = invoke({ ...lower(program, input), environment: { [name]: "" } });
    assert.equal(result.record.key, null);
    assert.match(result.record.ineligible ?? "", eligible ? /child LD_/ : /macOS and Linux only|child LD_/);
  }
  process.stdout.write("DYLD and LD overrides: Node and stage-child environments execute without keys\n");
}

{
  // Large streams: a stage printing 40 MiB on standard output and 20 MiB on
  // standard error finishes, and its invocation again replays both, byte
  // for byte; the streams are files, bounded by the file system alone.
  freshStore("large-streams");
  const big = Buffer.alloc(20 * 1024 * 1024);
  for (let i = 0; i < big.length; i++) big[i] = 32 + (i * 7919) % 95;
  const input = join(dir, "large.json");
  writeFileSync(input, big);
  const program = script("large.sh", '/bin/cat "$2"; /bin/cat "$2"; /bin/cat "$2" >&2');
  const first = invoke(lower(program, input));
  assert.equal(first.record.execution, "executed", first.error?.message);
  assert.equal(first.status, 0);
  assert.ok(first.stdoutBytes.equals(Buffer.concat([big, big])), "the whole standard output");
  assert.ok(first.stderrBytes.equals(big), "the whole standard error");
  const again = invoke(lower(program, input));
  assert.equal(again.record.execution, replayExecution);
  assert.ok(again.stdoutBytes.equals(first.stdoutBytes) && again.stderrBytes.equals(first.stderrBytes),
    "the replayed streams are the executed ones");
  process.stdout.write("large streams: 40 MiB standard output and 20 MiB standard error, executed and replayed\n");
}

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
  const program = script("slow.sh", `/bin/sleep 0.6; /bin/cat "$2"`, ["/bin/cat", "/bin/sleep"]);
  const input = file("slow.json", "slow");
  const timed = invoke(lower(program, input), 300);
  assert.equal(timed.record.execution, "timed-out");
  assert.ok(timed.record.key !== null);
  const reused = invoke(lower(program, input), 300);
  assert.equal(reused.record.execution, "timeout-replayed");
  assert.equal(reused.record.replay?.stored.attempt, timed.record.attempt);
  assert.equal(reused.record.replay?.stored.limitMs, 300);
  assert.equal(invoke(lower(program, input), 200).record.execution, "timeout-replayed", "a smaller limit");
  // Retrying timeouts executes the stage again at the same limit.
  process.env["TSCERT_RETRY_TIMEOUTS"] = "1";
  const retried = invoke(lower(program, input), 300);
  assert.equal(retried.record.execution, "timed-out", "a retried timeout executes");
  assert.notEqual(retried.record.attempt, timed.record.attempt);
  delete process.env["TSCERT_RETRY_TIMEOUTS"];
  assert.equal(invoke(lower(program, input), 300).record.execution, "timeout-replayed", "unretried, it is reused");
  const longer = invoke(lower(program, input), 5_000);
  assert.equal(longer.record.execution, "executed", "a longer limit executes past the observation");
  assert.equal(longer.stdout, "slow");
  assert.equal(invoke(lower(program, input), 300).record.execution, "replayed", "the finished result first");
  process.env["TSCERT_RETRY_TIMEOUTS"] = "1";
  assert.equal(invoke(lower(program, input), 300).record.execution, "replayed", "retrying, a finished result replays");
  delete process.env["TSCERT_RETRY_TIMEOUTS"];
  process.stdout.write("timeouts: reused at their limit or below, executed past at a longer one, executed again when " +
    "retried; finished results replay\n");
}

{
  // The runner (`pipeline/runner/stage-runner.c`) passes the program's
  // output bytes, exit status and signal through unchanged, reports its CPU
  // time, and on a timeout leaves no process of the stage running.
  freshStore("runner");
  const bytes = String.raw`printf 'out\000\377\376 \342\202\254\n'; printf 'err\000\200\n' >&2`;
  const cases: [string, string][] = [["exits", `${bytes}; exit 2`], ["succeeds", bytes],
    ["signals", `${bytes}; kill -USR1 $$`]];
  for (const [name, body] of cases) {
    const program = script(`runner-${name}.sh`, body, ["/usr/bin/printf"]);
    const input = file(`runner-${name}.json`, name);
    const staged = invoke(lower(program, input), 10_000, true);
    const direct = spawnSync(program, ["--lower-control-flow", input]);
    assert.deepEqual(staged.stdoutBytes, direct.stdout, `${name}: stdout`);
    assert.deepEqual(staged.stderrBytes, direct.stderr, `${name}: stderr`);
    assert.equal(staged.status, direct.status, `${name}: status`);
    assert.equal(staged.signal, direct.signal, `${name}: signal`);
    assert.ok("userMs" in staged.record.cpu, `${name}: CPU time`);
  }
  const missing = invoke(lower(join(dir, "no-such-program"), file("runner-missing.json", "")), 10_000, true);
  assert.equal(missing.record.execution, "failed");
  assert.equal(missing.error && "code" in missing.error ? missing.error.code : null, "ENOENT");
  // A busy program's CPU time and peak memory; a timed-out one's CPU time up to its kill, and its
  // descendants killed with it.
  const busy = invoke(lower(script("runner-busy.sh", "i=0; while [ $i -lt 100000 ]; do i=$((i+1)); done"),
    file("runner-busy.json", "")), 10_000, true);
  assert.ok("userMs" in busy.record.cpu && busy.record.cpu.userMs > 20 && (busy.record.cpu.peakBytes ?? 0) > 0,
    JSON.stringify(busy.record.cpu));
  const wait = (ms: number): Promise<void> => new Promise((done) => setTimeout(done, ms));
  const alive = (pid: number): boolean => {
    try {
      process.kill(pid, 0);
      return true;
    } catch {
      return false;
    }
  };
  /** Whether process `pid` ends within 2 s. */
  const ends = async (pid: number): Promise<boolean> => {
    for (let i = 0; i < 100 && alive(pid); i++) await wait(20);
    return !alive(pid);
  };
  const pidOf = (path: string): number => {
    const pid = Number(readFileSync(path, "utf8"));
    assert.ok(pid > 0, path);
    return pid;
  };
  /** A timeout the runner decided at its own deadline, not spawnSync's
   * backstop, which reports ETIMEDOUT; with the CPU time up to the kill. */
  const runnerTimeout = (name: string, held: Invoked): void => {
    assert.equal(held.record.execution, "timed-out", name);
    assert.equal(held.error, undefined, `${name}: ${String(held.error)}`);
    assert.ok("userMs" in held.record.cpu, `${name}: ${JSON.stringify(held.record.cpu)}`);
  };
  const pids = join(dir, "runner-pids");
  const spinning = script("runner-timeout.sh", `/bin/sleep 30 & echo $! > ${pids}; while :; do :; done`,
    ["/bin/sleep"]);
  // Each limit leaves the shell time to start and write its pid file under
  // load; every program runs far past it.
  const timed = invoke(lower(spinning, file("runner-timeout.json", "")), 2_000, true);
  runnerTimeout("spinning", timed);
  assert.ok("userMs" in timed.record.cpu && timed.record.cpu.userMs > 10, JSON.stringify(timed.record.cpu));
  assert.ok(await ends(pidOf(pids)), "a descendant of a timed-out stage survived");
  // The limit holds against a program ignoring SIGTERM, a stopped one and
  // one that left the group: each is killed by its process id 250 ms past it.
  const left = join(dir, "runner-setsid-pid");
  const held: { name: string; body: string; dependencies: string[]; limit: number }[] = [
    { name: "ignoring", body: 'trap "" TERM; /bin/sleep 5; exit 7', dependencies: ["/bin/sleep"], limit: 300 },
    { name: "stopped", body: "kill -STOP $$", dependencies: [], limit: 300 },
    { name: "setsid", dependencies: ["/usr/bin/perl"], limit: 2_000,
      body: `echo $$ > ${left}; exec /usr/bin/perl -e 'use POSIX; POSIX::setsid() or die "setsid"; sleep 30'` },
  ];
  for (const { name, body, dependencies, limit } of held) {
    if (!dependencies.every((d) => existsSync(d))) continue;
    runnerTimeout(name, invoke(lower(script(`runner-${name}.sh`, body, dependencies), file(`runner-${name}.json`, "")),
      limit, true));
  }
  if (existsSync("/usr/bin/perl")) assert.ok(await ends(pidOf(left)), "a program that left its group survived its limit");
  // A descendant holding the output pipes ends with the program.
  const lingering = invoke(lower(script("runner-lingering.sh", "/bin/sleep 30 & exit 0", ["/bin/sleep"]),
    file("runner-lingering.json", "")), 10_000, true);
  assert.equal(lingering.status, 0);
  assert.ok(lingering.record.elapsedMs < 3_000, `lingering: ${lingering.record.elapsedMs} ms`);
  // The runner killed, its watchdog kills the stage's group.
  const started = join(dir, "runner-orphan-pid");
  const orphan = script("runner-orphan.sh", `echo $$ > ${started}; exec /bin/sleep 30`, ["/bin/sleep"]);
  const report = openSync(join(dir, "runner-orphan-report"), "w+");
  const runner = spawn(runnerBuild, ["10000", String(2 ** 33), orphan], { stdio: ["ignore", "ignore", "ignore", report] });
  const exited = new Promise<void>((done) => runner.on("exit", () => done()));
  for (let i = 0; i < 100 && !existsSync(started); i++) await wait(20);
  const program = pidOf(started);
  runner.kill("SIGKILL");
  await exited;
  closeSync(report);
  assert.ok(await ends(program), "the program of a killed runner survived");
  // A program over the memory limit is stopped, and the report names the
  // memory read; under the limit the same program finishes.
  if (existsSync("/usr/bin/perl")) {
    const hungry = ["-e", `$x = "a" x 600_000_000; sleep 3; print "done"`];
    const overLimit = spawnSync(runnerBuild, ["20000", String(100 * 2 ** 20), "/usr/bin/perl", ...hungry],
      { stdio: ["ignore", "pipe", "ignore", "pipe"], encoding: "utf8" });
    const said = String(overLimit.output[3]);
    assert.ok(/^memory \d+$/m.test(said) && !/^deadline$/m.test(said), `memory limit report: ${said}`);
    assert.equal(overLimit.stdout, "", "a program over its memory limit finished");
    const underLimit = spawnSync(runnerBuild, ["20000", String(2 ** 32), "/usr/bin/perl", ...hungry],
      { stdio: ["ignore", "pipe", "ignore", "pipe"], encoding: "utf8" });
    assert.equal(underLimit.stdout, "done", "a program under its memory limit was stopped");
    assert.ok(!/^memory /m.test(String(underLimit.output[3])), "a program under its memory limit was reported over it");
  }
  process.stdout.write("runner: output bytes, status and signal pass through; CPU time reported, up to a timeout's " +
    "kill at the runner's own deadline, which leaves no process of the stage running, also of a program ignoring " +
    "SIGTERM, stopped or out of its group; descendants end with the program; a killed runner's stage is killed; " +
    "a program over its memory limit is stopped and reported\n");
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
  // Every manifest field returned to a caller belongs to its integrity
  // digest, including the refusal status and the stored measurement.
  const store = freshStore("manifest-integrity");
  const program = script("refusal.sh", 'echo "reject: control"; echo "end of refusal"; exit 1');
  const call = verifierCall(program, ["--check-units", file("integrity-fragment.json", "fragment"),
    file("integrity-claims.json", "claims"), "key", file("integrity-evidence.json", "evidence")]);
  const first = invoke(call);
  assert.equal(first.status, 1);
  assert.ok(first.record.key !== null);
  assert.equal(invoke(call).record.execution, "replayed");
  const path = join(store.root, "entries", "check", first.record.key, "manifest.json");
  const original = readFileSync(path, "utf8");
  chmodSync(path, 0o644);
  for (const corrupted of [
    original.replace('"exitStatus":1', '"exitStatus":0'),
    original.replace(/"elapsedMs":[^,}]+/, '"elapsedMs":-1'),
  ]) {
    assert.notEqual(corrupted, original);
    writeFileSync(path, corrupted);
    const fresh = invoke(call);
    assert.equal(fresh.record.execution, "executed", "a changed manifest payload is a miss");
    assert.equal(fresh.status, 1, "the fresh refusal reaches the caller");
    assert.equal(readFileSync(path, "utf8"), corrupted, "an invalid entry is not replaced");
  }
  process.stdout.write("manifest integrity: changed exit status or measurement is a miss and is not replaced\n");
}

/** A child process of this test, its status and output: for a section
 * running beside others. */
const childRun = (args: readonly string[], env: NodeJS.ProcessEnv, options: readonly string[] = []):
    Promise<{ status: number | null; stdout: string; stderr: string }> => new Promise((done, fail) => {
  const p = spawn(process.execPath, [...options, import.meta.filename, ...args], { env });
  let stdout = "", stderr = "";
  p.stdout.setEncoding("utf8");
  p.stderr.setEncoding("utf8");
  p.stdout.on("data", (text: unknown) => { stdout += String(text); });
  p.stderr.on("data", (text: unknown) => { stderr += String(text); });
  p.on("error", fail);
  p.on("close", (status: number | null) => done({ status, stdout, stderr }));
});

// The sections below wait on child processes: they run at once, each in a
// store of its own, naming it before each invocation of its own.
const sections: Promise<void>[] = [];
if (eligible) sections.push((async (): Promise<void> => {
  // Concurrent publication by two processes: both execute, one publishes,
  // the other finds the same result present; a stage giving two results for
  // one key is a store error.
  const child = (program: string, input: string): Promise<string> => new Promise((done, fail) => {
    const p = spawn(process.execPath, [import.meta.filename, "--child", program, input],
      { env: { ...process.env, TSCERT_STAGE_STORE: store.root } });
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
  // One run executes; the other executes too when the two overlap, and
  // replays the first's published result when load delays its start.
  // Either way both give the same output.
  const executed = JSON.stringify({ execution: "executed", stdout: "same" });
  const replayed = JSON.stringify({ execution: "replayed", stdout: "same" });
  const runs = both.map((out) => JSON.stringify(parsed(out)));
  assert.ok(runs.every((r) => r === executed || r === replayed), runs.join(" "));
  assert.ok(runs.includes(executed), runs.join(" "));
  assert.equal(readdirSync(join(store.root, "entries", "lower")).length, 1);
  use(store);
  assert.equal(invoke(lower(steady, input)).record.execution, "replayed");
  const varying = script("varying.sh", `/bin/sleep 1; echo $$`, ["/bin/sleep"]);
  const outcomes = (await Promise.all([child(varying, input), child(varying, input)])).map(parsed);
  assert.equal(outcomes.filter((o) => typeof o === "object" && o !== null && "error" in o && o.error === "store").length, 1, JSON.stringify(outcomes));
  process.stdout.write("concurrent publication: one entry for two writers; two results for one key a store error\n");
})());


sections.push((async (): Promise<void> => {
  const store = new Store(join(dir, "killed-writer"));
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
})());
for (const order of [["timeout", "finished"], ["finished", "timeout"]]) sections.push((async (): Promise<void> => {
  const store = new Store(join(dir, "race-" + order.join("-")));
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
})());
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
if (eligible) sections.push((async (): Promise<void> => {
  const store = new Store(join(dir, "interrupted-invocation"));
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
  use(store);
  assert.equal(invoke(lower(program, input)).record.execution, "executed", "dead writer never published");
  assert.equal(invoke(lower(program, input)).record.execution, "replayed");
  store.clean();
  assert.equal(existsSync(held.directory), false);
})());
// The two orders one after the other: they share their stand-in and logs.
if (eligible) sections.push((async (): Promise<void> => {
for (const order of [["timeout", "finished"], ["finished", "timeout"]]) {
  const store = new Store(join(dir, "invocation-race-" + order.join("-")));
  const program = script("race.sh", '/bin/sleep 0.6; /bin/cat "$2"', ["/bin/cat", "/bin/sleep"]);
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
  use(store);
  const later = invoke(lower(program, input), 300);
  assert.equal(later.record.execution, "replayed");
  assert.equal(later.stdout, "whole");
  process.stdout.write(`actual invocation race ${order.join(" then ")}: finished result replays\n`);
}
})());
if (platform() === "darwin") {
  // Minimal Mach-O load commands give a real dependency graph to traverse
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
  // Universal files: slices at 4096 and 8192, the second described in the
  // table or, as dyld also reads it, right after a table of one.
  const universal = (path: string, counted: number, slices: readonly (readonly string[])[]): void => {
    const table = Buffer.alloc(4096);
    table.writeUInt32BE(0xcafebabe, 0);
    table.writeUInt32BE(counted, 4);
    const images = slices.map((dependencies, i) => {
      const slice = join(dir, `slice-${i}`);
      macho(slice, dependencies);
      const bytes = readFileSync(slice);
      table.writeUInt32BE(i === 0 ? 0x01000007 : 0x0100000c, 8 + 20 * i);
      table.writeUInt32BE(4096 * (i + 1), 8 + 20 * i + 8);
      table.writeUInt32BE(bytes.length, 8 + 20 * i + 12);
      return Buffer.concat([bytes, Buffer.alloc(4096 - bytes.length)]);
    });
    writeFileSync(path, Buffer.concat([table, ...images]));
  };
  const fat = join(dir, "universal");
  universal(fat, 2, [[library], [library]]);
  assert.ok(typeof linkedLibraries(fat) !== "string", "a universal file whose architectures agree is identified");
  universal(fat, 2, [[library], [other]]);
  assert.match(String(linkedLibraries(fat)), /architectures differ/, "architectures loading different libraries");
  universal(fat, 1, [[library], [other]]);
  assert.match(String(linkedLibraries(fat)), /architectures differ/, "an arm64 slice after the table is read");
  process.stdout.write("linked libraries: a library replaced or relinked changes the identity; a universal file's architectures must agree\n");
} else if (platform() === "linux") {
  // The loader's own list: Node loads its interpreter and the C library.
  const node = linkedLibraries(process.execPath);
  assert.ok(typeof node !== "string", String(node));
  const listed = canonical(node);
  assert.match(listed, /ld-linux/, "the program interpreter is identified");
  assert.match(listed, /libc\.so/, "the C library is identified");
  const notElf = join(dir, "not-elf");
  writeFileSync(notElf, "#!/bin/sh\n# a script, which no ELF header starts\n");
  assert.match(String(linkedLibraries(notElf)), /ELF header/, "a file that is no ELF file is not identified");
  process.stdout.write("linked libraries: the loader's list names the interpreter and the C library; a file that is no ELF file has none\n");
}
{
  // Each identity control owns the modules it edits. An edit of a keyed
  // module (the stage's own, an execution adapter, a module nothing imports
  // by name) or a new module makes the stage execute without a key; an edit
  // of the replay policy or the store, which no key covers, replays the
  // entry at the same key.
  const keyed = new Map([["claims-assembly.mts", true], ["in-process-execution.mts", true],
    ["stage-execution.mts", true], ["hidden.mts", true], ["new-module.mts", true], ["stages.mts", false],
    ["stage-store.mts", false]]);
  const scenarios = ["in-process", "process"].flatMap((kind) => [
    ...[...keyed].map(([name, eligible]) => ({ kind, name, mode: eligible &&
      !(kind === "process" && ["claims-assembly.mts", "in-process-execution.mts"].includes(name)) ? "keyed" : "policy", off: false })),
    ...[false, true].flatMap((off) => (kind === "process" ? ["during", "timeout"] : ["during"])
      .map((mode) => ({ kind, name: "hidden.mts", mode, off }))),
  ]);
  const drivers = scenarios.map(({ kind, name, mode, off }, index) => {
    const root = join(dir, "loaded-copy-" + index);
    const copied = join(root, "pipeline");
    mkdirSync(copied, { recursive: true });
    symlinkSync(resolve(import.meta.dirname, "../tools"), join(root, "tools"));
    for (const module of ["claims-assembly.mts", "stages.mts", "stage-store.mts", "run-directory.mts",
      "stage-execution.mts", "in-process-execution.mts"])
      copyFileSync(resolve(import.meta.dirname, "../pipeline", module), join(copied, module));
    symlinkSync(resolve(import.meta.dirname, "../pipeline/runner"), join(copied, "runner"));
    // A module loaded only by a name the code computes.
    writeFileSync(join(copied, "hidden.mts"), 'const n = 1 / "/"; await import(name); const s = "//";\n');
    const driver = join(copied, "test.mts");
    writeFileSync(driver, String.raw`
import assert from "node:assert/strict";
import { appendFileSync, chmodSync, readFileSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { assemblyCall } from "./claims-assembly.mts";
import { invokeInProcess, invokeProcess, Recorder } from "./stages.mts";
import { auditForTests, verifierCall } from "./stage-execution.mts";
const target = new URL(process.argv[2], import.meta.url);
const kind = process.argv[5];
const during = ["during", "timeout"].includes(process.argv[3]);
const timeout = process.argv[3] === "timeout";
const original = during ? readFileSync(target) : null;
const program = new URL("stand-in.sh", import.meta.url).pathname;
const input = new URL("input.json", import.meta.url).pathname;
const marker = new URL("edited", import.meta.url).pathname;
writeFileSync(input, '{"modules":[]}');
// The marker lets a second invocation finish with exactly the same program
// and inputs, exposing either a finished result or a timeout published by
// the first invocation. Only the copied keyed module is edited.
writeFileSync(program, '#!/bin/sh\n' + (during
  ? 'if [ ! -f "' + marker + '" ]; then\n' +
    'printf "\\n// edited during execution\\n" >> "' + target.pathname + '"\n' +
    ': > "' + marker + '"\n' + (timeout ? '/bin/sleep 30\n' : '') + 'fi\n'
  : '') + '/bin/cat "$2"\n');
chmodSync(program, 0o755);
auditForTests(program, ["/bin/cat", "/bin/sleep"]);
const recorder = new Recorder(null);
let edit = during;
const run = (): ReturnType<typeof invokeInProcess<string>> => {
  if (kind === "process") {
    const result = invokeProcess(verifierCall(program, ["--lower-control-flow", input]),
      // These drivers start together beside the other fast checks. Allow
      // the shell time to reach its edit before the timeout kills it.
      { limitMs: timeout ? 5_000 : 10_000, force: false, recorder });
    return { value: result.stdout, record: result.record };
  }
  const call = assemblyCall('{"modules":[]}', []);
  return invokeInProcess({ ...call, run: () => {
    if (edit) {
      appendFileSync(target, "\n// edited during execution\n");
      edit = false;
    }
    return call.run();
  } }, { force: false, recorder });
};
if (during) {
  const setting = process.env.TSCERT_STAGE_STORE;
  const result = run();
  assert.equal(result.record.execution, timeout ? "timed-out" : "executed");
  assert.equal(result.record.key, null);
  assert.equal(result.record.ineligible, "loaded node-side modules differ from disk");
  assert.deepEqual(recorder.records, [result.record]);
  assert.equal(result.record.forced, setting === "off");
  assert.equal(result.record.exitStatus, kind === "process" && !timeout ? 0 : null);
  if (!timeout) assert.equal(result.value, '{"modules":[]}');
  // Restore the captured identity and enable the store so the same key
  // would find either kind of publication, including from a store-off run.
  writeFileSync(target, original);
  process.env.TSCERT_STAGE_STORE = process.argv[4];
  const later = run();
  assert.equal(later.record.execution, "executed");
  assert.notEqual(later.record.key, null);
  assert.equal(later.record.ineligible, null);
  assert.deepEqual(later.record.manifest, result.record.manifest);
  assert.equal(later.value, '{"modules":[]}');
  assert.equal(run().record.execution, "replayed");
  process.exit(0);
}
if (process.argv[3] === "fresh-policy") {
  assert.equal(process.env.TSCERT_EDITED_POLICY, "loaded");
  const result = run();
  assert.equal(result.value, '{"modules":[]}');
  assert.equal(result.record.execution, "replayed");
  assert.equal(result.record.key, process.argv[4]);
  process.exit(0);
}
const firstResult = run();
assert.equal(firstResult.record.execution, "executed");
const first = firstResult.record.key;
assert.notEqual(first, null);
assert.equal(run().record.execution, "replayed");
appendFileSync(new URL(process.argv[2], import.meta.url), "\n// edited during worker lifetime\n");
const result = run();
assert.equal(result.value, '{"modules":[]}');
if (process.argv[3] === "keyed") {
  assert.equal(result.record.execution, "executed");
  assert.equal(result.record.key, null);
  assert.match(result.record.ineligible ?? "", /loaded .*modules differ from disk/);
} else {
  assert.equal(result.record.execution, "replayed");
  assert.equal(result.record.key, first);
  appendFileSync(new URL(process.argv[2], import.meta.url),
    '\nprocess.env.TSCERT_EDITED_POLICY = "loaded";\n');
  const fresh = spawnSync(process.execPath, [import.meta.filename, process.argv[2], "fresh-policy", first, kind],
    { encoding: "utf8" });
  assert.equal(fresh.status, 0, fresh.stderr);
}
`);
    return { name, driver, kind, mode, off, store: join(root, "store") };
  });
  const program = script("runtime.sh", '/bin/cat "$2"');
  const input = file("runtime.json", "runtime"), preload = file("preload.mjs", "");
  const env = { ...process.env, TSCERT_STAGE_STORE: join(dir, "loaded-copy-store") };
  const options = [["--import", preload], ["--require", preload], ["--experimental-loader", preload], ["--experimental_loader", preload], ["-r", preload]];
  sections.push((async (): Promise<void> => {
    const children = await Promise.all([
      ...drivers.map(({ name, driver, kind, mode, off, store }) => new Promise<{ status: number | null; stderr: string }>((done, fail) => {
        const p = spawn(process.execPath, [driver, "./" + name, mode, store, kind],
          { env: { ...env, TSCERT_STAGE_STORE: off ? "off" : store } });
        let stderr = "";
        p.stderr.setEncoding("utf8");
        p.stderr.on("data", (text: unknown) => { stderr += String(text); });
        p.on("error", fail);
        p.on("close", (status: number | null) => done({ status, stderr }));
      })),
    ]);
    for (const child of children) assert.equal(child.status, 0, child.stderr);
    const preloaded = await Promise.all(options.map((args) => childRun(["--runtime-child", program, input], env, args)));
    for (const [i, child] of preloaded.entries()) {
      assert.equal(child.status, 0, child.stderr);
      const [record] = readInvocationLog(file(`runtime-log-${i}.jsonl`, JSON.stringify({ event: "end", record: JSON.parse(child.stdout) }) + "\n"));
      assert.equal(record.key, null);
      assert.equal(record.execution, "executed");
      assert.match(record.ineligible ?? "", /Node import, require or loader/);
    }
    const child = await childRun(["--runtime-child", program, input], { ...env, NODE_OPTIONS: `--import="${preload}"` });
    assert.equal(child.status, 0, child.stderr);
    assert.match(child.stdout, /Node import, require or loader/);
    process.stdout.write("loaded code and Node preload options: changed or unidentified dependencies execute without a key; a changed replay policy replays\n");
  })());
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
// Eviction (STAGE-STORE.md, "Location and size"): a pass removes the least
// recently used entries within the budget, an entry with its references,
// and measures what no use line names; a snapshot a running process holds
// stays; a replay racing an eviction is a miss, never another result.
{
  const store = new Store(join(dir, "evict-lru"));
  const old = Array.from({ length: 10 }, (_, i) => `old ${i}`), fresh = Array.from({ length: 10 }, (_, i) => `new ${i}`);
  storeOp(store, "publish", ...old);
  storeOp(store, "publish", ...fresh);
  storeOp(store, "replay", ...old.slice(0, 3));
  const entry = onDisk(join(store.root, "entries", "lower", sha256(old[0])));
  assert.equal(onDisk(store.root, "entries"), 20 * entry);
  const budget = 12 * entry;
  const pass = store.evictionPass(budget);
  assert.ok(pass);
  const kept = new Set(readdirSync(join(store.root, "entries", "lower")));
  const survives = (input: string): boolean => kept.has(sha256(input));
  assert.deepEqual(old.map(survives), [true, true, true, false, false, false, false, false, false, false],
    "the replayed entries outlive the newer ones");
  assert.equal(fresh.filter(survives).length, 6, "the oldest of the newer entries go next");
  assert.equal(pass.evicted.entries, 11);
  assert.equal(pass.afterBytes, onDisk(store.root, "entries"));
  assert.ok(pass.afterBytes <= budget * 0.8, `${pass.afterBytes} within the budget's low water`);
  // A store whose use logs are gone is measured whole: the same bytes.
  rmSync(join(store.root, "uses"), { recursive: true });
  const measured = store.evictionPass(budget);
  assert.equal(measured?.measured, 9);
  assert.equal(measured?.afterBytes, pass.afterBytes);
  assert.equal(measured?.evicted.entries, 0);
}
{
  const store = new Store(join(dir, "evict-references"));
  storeOp(store, "observed", "observed input");
  const references = join(store.root, "observed", "parse");
  assert.equal(readdirSync(references).length, 1);
  const pass = store.evictionPass(0);
  assert.deepEqual([pass?.evicted.entries, pass?.evicted.references], [1, 1]);
  assert.deepEqual(readdirSync(references), [], "the reference and its pre-key directory go with the entry");
  assert.deepEqual(readdirSync(join(store.root, "entries", "parse")), []);
}
{
  const store = new Store(join(dir, "evict-snapshots"));
  const held = store.stableDirectory("sources", [["source.ts", Buffer.from("held by this process")]]);
  const left = storeOp(store, "snapshot", "made by a stopped process").trim();
  storeOp(store, "publish", "an entry");
  assert.ok(held && existsSync(left));
  const pass = store.evictionPass(0);
  assert.deepEqual([pass?.held, pass?.evicted.sources, pass?.evicted.entries], [1, 1, 1]);
  assert.ok(existsSync(held), "a snapshot a running process holds stays");
  assert.ok(!existsSync(left), "one no running process holds goes");
  const again = storeOp(store, "snapshot", "made by a stopped process").trim();
  assert.equal(again, left, "a snapshot is published again at its location");
  store.clean();
  assert.ok(existsSync(held) && !existsSync(again), "cleanup removes the snapshots no running process holds");
  assert.equal(store.stableDirectory("sources", [["source.ts", Buffer.from("held by this process")]]), held);
}
{
  // The orchestrators' start: a due pass runs in a process of its own, and
  // leaves the store within its budget.
  const store = new Store(join(dir, "evict-started"));
  storeOp(store, "publish", ...Array.from({ length: 10 }, (_, i) => `started ${i}`));
  const budget = 4 * onDisk(join(store.root, "entries", "lower", sha256("started 0")));
  assert.ok(store.evictionDue(), "a store no pass has seen");
  const saved = { store: process.env["TSCERT_STAGE_STORE"], budget: process.env["TSCERT_STORE_BUDGET"] };
  process.env["TSCERT_STAGE_STORE"] = store.root;
  process.env["TSCERT_STORE_BUDGET"] = String(budget);
  startEviction();
  process.env["TSCERT_STAGE_STORE"] = saved.store;
  if (saved.budget === undefined) delete process.env["TSCERT_STORE_BUDGET"];
  else process.env["TSCERT_STORE_BUDGET"] = saved.budget;
  const started = Date.now();
  while (!existsSync(join(store.root, "uses", "base")) || existsSync(join(store.root, "eviction"))) {
    assert.ok(Date.now() - started < 30_000, "the started pass finishes");
    Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 50);
  }
  assert.ok(onDisk(store.root, "entries") <= budget, "within the budget after the pass");
  assert.equal(store.evictionDue(), false, "the next pass waits for its interval");
}
sections.push((async (): Promise<void> => {
  // A replay racing an eviction: a reader replays one entry while this
  // process publishes it and a pass removes it, over and over.
  const store = new Store(join(dir, "evict-race"));
  const input = "raced input";
  evictable(store, "lower", input);
  const stop = join(dir, "evict-race-stop");
  const reader = spawn(process.execPath, [import.meta.filename, "--store-op", store.root, "read", input, stop]);
  let out = "";
  reader.stdout.setEncoding("utf8");
  const ready = new Promise<void>((done) => {
    reader.stdout.on("data", (text: unknown) => {
      out += String(text);
      if (out.startsWith("ready\n")) done();
    });
  });
  const closed = new Promise<void>((done, fail) => {
    reader.on("error", fail);
    reader.on("close", () => done());
  });
  await ready;
  // A fixed number of rounds, each a publication, a pause the reader
  // replays in, and a pass removing the entry.
  let passes = 0;
  for (let round = 0; round < 100; round++) {
    evictable(store, "lower", input);
    await new Promise((done) => setTimeout(done, 5));
    if (store.evictionPass(0)) passes++;
    await new Promise((done) => setTimeout(done, 5));
  }
  writeFileSync(stop, "");
  await closed;
  out = out.slice("ready\n".length).trim();
  const counts: unknown = JSON.parse(out);
  assert.ok(typeof counts === "object" && counts !== null && "wrong" in counts && "hits" in counts && "misses" in counts);
  assert.equal(counts.wrong, 0, out);
  assert.ok(Number(counts.hits) > 0 && Number(counts.misses) > 0 && passes > 0, `${out}, ${passes} passes`);
  process.stdout.write(`eviction: least recently used entries first, within the budget; references with their entry; ` +
    `held snapshots stay; a replay racing ${passes} passes is a miss or the entry's result (${out})\n`);
})());
{
  // A use while a running process removes snapshots does without the
  // store's snapshot, at once; a marker of a stopped process is no removal.
  // A pass's own marker goes when it ends, another's stays.
  const store = new Store(join(dir, "evict-marker"));
  const id = (): string => randomUUID().slice(0, 8);
  mkdirSync(join(store.root, "evicting"), { recursive: true });
  const stoppedMarker = join(store.root, "evicting", `${hostname()}.${stoppedPid()}.${id()}`);
  writeFileSync(stoppedMarker, "");
  const ordinary = storeOp(store, "snapshot", "a use beside a stopped marker").trim();
  assert.ok(existsSync(ordinary), "a stopped process's marker is no removal");
  const runningMarker = join(store.root, "evicting", `${hostname()}.${process.pid}.${id()}`);
  writeFileSync(runningMarker, "");
  const started = Date.now();
  assert.equal(storeOp(store, "snapshot", "a use during a removal").trim(), "null", "the use does without the store's snapshot");
  assert.ok(Date.now() - started < 10_000, "and does not wait");
  const pass = store.evictionPass(0);
  assert.equal(pass?.evicted.sources, 1);
  assert.ok(!existsSync(ordinary), "a pass removes snapshots beside another process's marker");
  assert.ok(existsSync(runningMarker), "another process's marker stays");
  assert.equal(storeOp(store, "snapshot", "a use during a removal").trim(), "null");
  rmSync(runningMarker);
  assert.notEqual(storeOp(store, "snapshot", "a use during a removal").trim(), "null");
}
{
  // The eviction lock: a lock is built whole and renamed into place, so one
  // present names its owner; a running owner's lock stops a pass, a stopped
  // owner's lock and a lock without an owner are taken over, and an
  // interrupted acquisition leaves a temporary the pass removes.
  const store = new Store(join(dir, "evict-lock"));
  storeOp(store, "publish", "locked entry");
  const lock = join(store.root, "eviction");
  const placeLock = (owner: string | null): void => {
    rmSync(lock, { recursive: true, force: true });
    mkdirSync(lock);
    writeFileSync(join(lock, owner === null ? "partial" : "owner"), owner ?? "");
  };
  placeLock(`${hostname()} ${process.pid} ${randomUUID().slice(0, 8)}`);
  assert.equal(store.evictionPass(0), null, "a running owner's lock stops a pass");
  assert.equal(store.evictionDue(), false);
  const interrupted = join(store.root, "tmp", hostname(), `${stoppedPid()}.lock-0000`);
  mkdirSync(interrupted, { recursive: true });
  placeLock(`${hostname()} ${stoppedPid()} ${randomUUID().slice(0, 8)}`);
  assert.equal(store.evictionPass(0)?.evicted.entries, 1, "a stopped owner's lock is taken over");
  assert.ok(!existsSync(lock) && !existsSync(interrupted), "the pass leaves no lock and no stopped temporary");
  placeLock(null);
  assert.ok(store.evictionPass(0), "a lock without an owner is taken over");
  // Another process takes the stale lock over between this pass's judgment
  // and its move: the pass finds the new owner, puts its lock back and
  // stops.
  const named = (): string => `${hostname()} ${process.pid} ${randomUUID().slice(0, 8)}`;
  const other = named();
  placeLock(`${hostname()} ${stoppedPid()} ${randomUUID().slice(0, 8)}`);
  pauseLockForTests((point) => {
    if (point !== "takeover") return;
    pauseLockForTests(null);
    placeLock(other);
  });
  assert.equal(store.evictionPass(0), null);
  assert.equal(readFileSync(join(lock, "owner"), "utf8"), other, "the other process keeps its lock");
  // A third process acquires the lock while the pass is putting the second's
  // back: the third keeps it, and the second's stays in the pass's
  // temporary directory, deleted by no one while the pass runs.
  const third = named();
  placeLock(`${hostname()} ${stoppedPid()} ${randomUUID().slice(0, 8)}`);
  pauseLockForTests((point) => {
    if (point === "takeover") placeLock(other);
    if (point === "restore") {
      pauseLockForTests(null);
      placeLock(third);
    }
  });
  assert.equal(store.evictionPass(0), null);
  assert.equal(readFileSync(join(lock, "owner"), "utf8"), third, "the third process keeps its lock");
  const temporaries = join(store.root, "tmp", hostname());
  assert.ok(readdirSync(temporaries).some((name) => name.includes(".lock-moved-") &&
    readFileSync(join(temporaries, name, "owner"), "utf8") === other), "the second's lock is moved aside, not deleted");
  // The holder's lock replaced before its release (its owner judged
  // stopped): the release leaves the replacement in place.
  rmSync(lock, { recursive: true });
  pauseLockForTests((point) => {
    if (point !== "release") return;
    pauseLockForTests(null);
    placeLock(other);
  });
  assert.ok(store.evictionPass(0));
  assert.equal(readFileSync(join(lock, "owner"), "utf8"), other, "a release removes only its own lock");
  rmSync(lock, { recursive: true });
}
{
  // A use around a removal's second read of the use logs: a use whose line
  // precedes that read keeps the store's snapshot; one after it does without
  // it, and the snapshot goes.
  const store = new Store(join(dir, "evict-reread"));
  const before = storeOp(store, "snapshot", "used before the read").trim();
  const after = storeOp(store, "snapshot", "used after the read").trim();
  const use = (text: string): string | null => store.stableDirectory("sources", [["source.ts", Buffer.from(text)]]);
  const uses: (string | null)[] = [];
  pauseLockForTests((point) => {
    if (point === "marked") uses.push(use("used before the read"));
    if (point === "reread") uses.push(use("used after the read"));
  });
  const pass = store.evictionPass(0);
  pauseLockForTests(null);
  assert.deepEqual(uses, [null, null], "each use during the removal does without the store's snapshot");
  assert.equal(pass?.evicted.sources, 1);
  assert.ok(existsSync(before), "a use recorded before the read keeps its snapshot");
  assert.ok(!existsSync(after), "one recorded after it does not");
}
{
  // Another host's owners count as running whatever their age: its use
  // log's snapshot stays and the log too, its marker stops uses, its lock
  // stops passes; a clean naming the host forgets them.
  const store = new Store(join(dir, "evict-remote"));
  const snapshot = storeOp(store, "snapshot", "held on another host").trim();
  const remote = "another-host.example";
  const old = new Date(Date.now() - 30 * 24 * 60 * 60_000);
  const log = join(store.root, "uses", `${remote}.4242.abcdef01`);
  writeFileSync(log, `${old.getTime()} 4096 sources/${basename(snapshot)}\n`);
  utimesSync(log, old, old);
  assert.equal(store.evictionPass(0)?.held, 1);
  assert.ok(existsSync(snapshot) && existsSync(log), "another host's hold and log stay");
  mkdirSync(join(store.root, "evicting"), { recursive: true });
  const marker = join(store.root, "evicting", `${remote}.4242.abcdef02`);
  writeFileSync(marker, "");
  utimesSync(marker, old, old);
  assert.equal(storeOp(store, "snapshot", "a use beside another host's marker").trim(), "null");
  const lock = join(store.root, "eviction");
  mkdirSync(lock);
  writeFileSync(join(lock, "owner"), `${remote} 4242 abcdef03`);
  utimesSync(lock, old, old);
  assert.equal(store.evictionPass(0), null, "another host's lock stops a pass");
  store.clean([remote]);
  assert.ok(![snapshot, log, marker, lock].some(existsSync), "a clean forgetting the host removes them");
  process.stdout.write("eviction: the lock is taken over, restored and released by its owner's id, through " +
    "concurrent takeovers; a use before a removal's second read keeps its snapshot; another host's owners " +
    "run until a clean forgets the host\n");
}
{
  // Each timeout observation is an item of its own.
  const store = new Store(join(dir, "evict-timeouts"));
  storeOp(store, "timeouts", "timed out", "attempt-1", "attempt-2", "attempt-3");
  const pass = store.evictionPass(1 << 30);
  assert.deepEqual([pass?.items, pass?.beforeBytes], [3, 3 * 4096]);
  assert.equal(store.evictionPass(0)?.evicted.timeouts, 3);
  assert.deepEqual(readdirSync(join(store.root, "timeouts", "lower")), [], "the key's emptied directory goes");
  process.stdout.write("eviction: a use during a removal does without the store's snapshot; markers are per process; " +
    "the lock is taken whole and over from a stopped or missing owner, never from a running one; " +
    "each timeout observation is an item\n");
}
await Promise.all(sections);
assert.throws(() => invoke(lower(script("any.sh", "/bin/cat \"$2\""), file("x.json", "x")), 0), /positive integer/);
process.stdout.write("limits: a stage's limit is a positive integer number of milliseconds\n");
