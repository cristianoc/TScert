// The stage store's tests (DESIGN.md, "The stage store"): dependency
// invalidation, concurrent publication by two processes, an interrupted
// writer, a timeout/success race, writable artifact isolation and a longer
// limit executing past a recorded timeout. The stages are shell-script
// stand-ins declared audited for the test, so no build is needed; the
// pipeline's own stages replay in `pipeline/test.mts`.
import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { chmodSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { hostname } from "node:os";
import { join } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { Store, StoreError } from "../pipeline/stage-store.mts";
import { auditForTests, invokeProcess, readInvocationLog, Recorder, verifierCall, type Invoked, type ProcessCall }
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
  assert.ok(first.record.key !== null, JSON.stringify(first.record.ineligible));
  assert.equal(first.stdout, "{}one");
  const again = invoke(lower(program, input), 10_000, false, recorder);
  assert.equal(again.record.execution, "replayed");
  assert.equal(again.record.key, first.record.key);
  assert.equal(again.stdout, "{}one");
  assert.ok(again.record.replay && again.record.replay.stored.attempt === first.record.attempt);
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
    ["executed", "replayed", "executed", "executed", "executed"]);
  assert.ok(readdirSync(join(store.root, "entries", "lower")).length >= 4);
  process.stdout.write("dependency invalidation: replayed at the same input, program and dependencies; executed otherwise\n");
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
  assert.equal(second.record.execution, "replayed");
  assert.equal(readFileSync(outputs[1], "utf8"), "fragmentclaims");
  writeFileSync(outputs[1], "changed by its caller");
  const third = invoke(search(program, outputs[2]));
  assert.equal(third.record.execution, "replayed");
  assert.equal(readFileSync(outputs[2], "utf8"), "fragmentclaims");
  assert.equal(readFileSync(outputs[0], "utf8"), "fragmentclaims");
  process.stdout.write("artifact isolation: a replayed output is the caller's own writable copy\n");
}

{
  // A timeout is an observation at its limit: reused at that limit or a
  // smaller one; a longer limit executes past it; the finished result it
  // publishes takes precedence over the observation, also over a timeout
  // observed later.
  const store = freshStore("timeouts");
  const program = script("slow.sh", `/bin/sleep 1; /bin/cat "$2"`, ["/bin/cat", "/bin/sleep"]);
  const input = file("slow.json", "slow");
  const timed = invoke(lower(program, input), 300);
  assert.equal(timed.record.execution, "timed-out");
  assert.ok(timed.record.key !== null);
  const key = timed.record.key;
  const reused = invoke(lower(program, input), 300);
  assert.equal(reused.record.execution, "timeout-replayed");
  assert.equal(reused.record.replay?.stored.attempt, timed.record.attempt);
  assert.equal(reused.record.replay?.stored.limitMs, 300);
  assert.equal(invoke(lower(program, input), 200).record.execution, "timeout-replayed", "a smaller limit");
  const longer = invoke(lower(program, input), 5_000);
  assert.equal(longer.record.execution, "executed", "a longer limit executes past the observation");
  assert.equal(longer.stdout, "slow");
  assert.equal(invoke(lower(program, input), 300).record.execution, "replayed", "the finished result first");
  // A timeout published after the finished result leaves it in place.
  const late = invoke(lower(program, input), 300, true);
  assert.equal(late.record.execution, "timed-out");
  assert.equal(readdirSync(join(store.root, "timeouts", "lower", key)).length, 2);
  assert.equal(invoke(lower(program, input), 300).record.execution, "replayed");
  process.stdout.write("timeouts: reused at their limit or below, executed past at a longer one; a finished result wins a race\n");
}

{
  // An interrupted writer: its temporary directory is never read, and a
  // later cleanup removes it only once its process is gone. A corrupt or
  // incomplete entry at a key's destination is a miss; the fresh result is
  // used and not published over it.
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
  const temporary = join(store.root, "tmp", hostname());
  mkdirSync(join(temporary, "999999999.stopped"), { recursive: true });
  writeFileSync(join(temporary, "999999999.stopped", "stdout"), "half");
  mkdirSync(join(temporary, `${process.pid}.running`));
  store.clean();
  assert.deepEqual(readdirSync(temporary), [`${process.pid}.running`]);
  assert.equal(invoke(lower(program, input)).record.execution, "executed");
  assert.equal(invoke(lower(program, input)).record.execution, "replayed");
  process.stdout.write("interrupted writers: an unpublished or corrupt entry is a miss; cleanup spares running writers\n");
}

{
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

assert.throws(() => invoke(lower(script("any.sh", "/bin/cat \"$2\""), file("x.json", "x")), 0), /positive integer/);
process.stdout.write("limits: a stage's limit is a positive integer number of milliseconds\n");
