// A failure of the tool is reported as one, never as a refusal, an absence
// or an unknown answer: at each kind of site that catches what a query
// throws, a forced failure (`force-tool-failure.mts`) surfaces as a tool
// failure, and the forcing is checked to have happened there.
import "./force-tool-failure.mts";
import assert from "node:assert/strict";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import fs, { chmodSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { syncBuiltinESMExports } from "node:module";
import { isHostFile } from "../tools/family-activation.mts";
import { join, resolve } from "node:path";
import { close as closeParser, parseFile } from "../tools/fragment-parse.mts";
import { messageOf } from "../tools/thrown.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { abandonCompiler, compilerProcess, openCompiler } from "../tools/compiler-channel.mts";
import { present } from "../tools/files.mts";
import { run as runStep } from "../pipeline/verify-source.mts";

const dir = runDirectory("tscert-tool-failures-");
const config = join(dir, "tsconfig.json");
writeFileSync(config, JSON.stringify({ compilerOptions: { strict: true, noEmit: true, module: "Node16",
  moduleResolution: "Node16" }, include: ["*.ts"] }));
writeFileSync(join(dir, "package.json"), JSON.stringify({ type: "module" }));
const fired = join(dir, "fired.txt");
process.env["TSCERT_FORCE_FIRED"] = fired;

/** The parse of `text` as `name` with the failure forced as `force` says:
 * its report, after checking the forcing happened. */
function forcedParse(name: string, text: string, force: Record<string, string>): string {
  const file = join(dir, name);
  writeFileSync(file, text);
  writeFileSync(fired, "");
  for (const [key, value] of Object.entries(force)) process.env[key] = value;
  let report = "";
  try {
    parseFile(file, false, config);
  } catch (error) {
    report = messageOf(error);
  } finally {
    for (const key of Object.keys(force)) delete process.env[key];
  }
  const requests = readFileSync(fired, "utf8");
  assert.ok(requests.length > 0, `${name}: the failure was not forced where ${JSON.stringify(force)} says`);
  assert.doesNotMatch(requests, /^later /m, `${name}: a request was sent on the channel after its failure`);
  return report;
}

const sites: { name: string; site: string; text: string; force: Record<string, string>; at?: string }[] = [
  { name: "contextual.ts", site: "a read refused into a value (a contextual parameter's type)",
    text: "declare function each(f: (v: number[]) => number): void;\nexport function g(): void {\n  each((v) => v.length);\n}\n",
    force: { TSCERT_FORCE_FRAME: "at readContextualTerm \\(" } },
  { name: "iterable.ts", site: "a read refused into a located error (an iterable's type)",
    text: "export function f(xs: number[]): number {\n  let t = 0;\n  for (const x of xs) t += x;\n  return t;\n}\n",
    force: { TSCERT_FORCE_FRAME: "at kindsOf \\(" }, at: "(line 3, col 19)" },
  { name: "alias.ts", site: "a lookup made an absence (the alias a reference names)",
    text: "type Id<T> = T;\nexport function f(x: Id<number>): number {\n  return x;\n}\n",
    force: { TSCERT_FORCE_FRAME: "at aliasOf \\([^)]*declaration-graph\\.mts" } },
  { name: "indexed.ts", site: "a computed type refused when generic (an indexed access)",
    text: "interface Box<T> {\n  a: T;\n}\nexport function f<T>(x: Box<T>): Box<T>[\"a\"] {\n  return x.a;\n}\n",
    force: { TSCERT_FORCE_FRAME: "at project \\([^)]*computed-types\\.mts" } },
  { name: "importer.ts", site: "an imported module left out (its lowering)",
    text: "import { one } from \"./lib.js\";\nexport function f(): number {\n  return one();\n}\n",
    force: { TSCERT_FORCE_PAYLOAD: join(dir, "lib.ts") } },
];
writeFileSync(join(dir, "lib.ts"), "export function one(): number {\n  return 1;\n}\n");
for (const { name, site, text, force, at } of sites) {
  const report = forcedParse(name, text, force);
  assert.match(report, /^tool failure: the front end exhausted the call stack/, `${site}: ${report}`);
  if (at) assert.ok(report.endsWith(at), `${site}: located at ${report}`);
  process.stdout.write(`${site}: a tool failure\n`);
}

// A failure after a request was sent leaves its reply unread: the failure
// is the report, the compilers are abandoned without a further request, and
// the next parse reads replies of its own.
const iterable = sites.find((s) => s.name === "iterable.ts")?.text ?? "";
// A source the declaration reader refuses where the compiler is open.
const refusedText = "export function f(): number {\n  return Math.random();\n}\n";
for (const [site, frame] of [["the parser's compiler", "at openFile \\("], ["the declaration reader's", "at kindsOf \\("]]) {
  const report = forcedParse("sent.ts", iterable, { TSCERT_FORCE_FRAME: frame ?? "", TSCERT_FORCE_AFTER_SEND: "1" });
  assert.match(report, /^tool failure: the front end exhausted the call stack/, `${site}, after a request was sent: ${report}`);
  writeFileSync(fired, "");
  const fresh = parseFile(join(dir, "sent.ts"), false, config);
  assert.ok(fresh.functions.length === 1, `a parse after ${site} failed lowers its function`);
  process.stdout.write(`${site}, failing after a request was sent: a tool failure, and the next parse as without it\n`);
}

// The file system failing where the front end reads a file is a tool
// failure, whatever the error's fields: reading an imported module denied as
// Node's permission model denies it (ERR_ACCESS_DENIED, no `syscall`), and
// EACCES resolving a path; a path that names nothing is the absence its
// reader gives a meaning.
{
  const failing = (call: string, path: string, code: string, fields: Record<string, string>) => (...args: unknown[]): unknown => {
    if (args[0] === path) throw Object.assign(new Error(`${code}: forced by tests/tool-failures.mts, ${call} '${path}'`), { code, ...fields });
    return undefined;
  };
  const read = fs.readFileSync, resolveReal = fs.realpathSync;
  const lib = join(dir, "lib.ts");
  const readFailure = failing("open", lib, "ERR_ACCESS_DENIED", { permission: "FileSystemRead", resource: lib });
  fs.readFileSync = Object.assign((...args: Parameters<typeof read>) => (readFailure(...args), read(...args)), read);
  syncBuiltinESMExports();
  let report = "";
  try {
    parseFile(join(dir, "importer.ts"), false, config);
  } catch (error) {
    report = messageOf(error);
  } finally {
    fs.readFileSync = read;
    syncBuiltinESMExports();
  }
  assert.match(report, /^tool failure: the file system failed \(called from [^)]+\): read [^:]*lib\.ts: ERR_ACCESS_DENIED: forced .*\(lowering the imported module \.\/lib\.ts\)$/, report);
  const denied = join(dir, "denied.d.ts");
  const resolveFailure = failing("realpath", denied, "EACCES", { syscall: "realpath" });
  fs.realpathSync = Object.assign((...args: Parameters<typeof resolveReal>) => (resolveFailure(...args), resolveReal(...args)), resolveReal);
  syncBuiltinESMExports();
  try {
    assert.throws(() => isHostFile(denied), /EACCES: forced/);
    assert.equal(isHostFile(join(dir, "absent.d.ts")), false, "a path naming nothing is no host file");
  } finally {
    fs.realpathSync = resolveReal;
    syncBuiltinESMExports();
  }
  // A path behind a directory the process may not search: the operating
  // system's EACCES, which `existsSync` reads as false, is no absence.
  const locked = join(dir, "locked");
  mkdirSync(locked);
  writeFileSync(join(locked, "claims.json"), "{}");
  chmodSync(locked, 0o000);
  try {
    assert.throws(() => present(join(locked, "claims.json")), /^Error: stat .*claims\.json: EACCES/);
  } finally {
    chmodSync(locked, 0o755);
  }
  assert.equal(present(join(locked, "absent.json")), false, "a path naming nothing is absent");
  closeParser();
  process.stdout.write("the file system failing under the front end: a tool failure; a path naming nothing, an absence\n");
}

// A native read failure, before or after the request was sent, is a tool
// failure of the request, wherever its stack's first frame is.
for (const after of ["", "1"]) {
  const report = forcedParse("io.ts", iterable, { TSCERT_FORCE_FRAME: "at kindsOf \\(", TSCERT_FORCE_KIND: "io",
    TSCERT_FORCE_AFTER_SEND: after });
  assert.match(report, /^tool failure: the compiler's API failed in Checker\.getTypeAtLocation .*EBADF: bad file descriptor, read/,
    `a native read failure${after ? " after the request was sent" : ""}: ${report}`);
}
process.stdout.write("a native read failure, before and after the request was sent: a tool failure\n");

// Releasing the compiler: a failure of the snapshot releases its close sends
// is reported as a tool failure, with what was in flight as context, and the
// compiler is abandoned without a further request.
for (const [name, text, context] of [["released.ts", iterable, "closing the compiler"],
  ["refused-release.ts", refusedText, "closing the compiler after: "]] as const) {
  const report = forcedParse(name, text, { TSCERT_FORCE_FRAME: "at releaseCompiler \\(", TSCERT_FORCE_KIND: "io" });
  assert.match(report, /^tool failure: the compiler's API failed in .*EBADF: bad file descriptor, read, /, report);
  assert.ok(report.includes(context), `${name}: ${report}`);
}
process.stdout.write("a failure releasing the compiler: a tool failure, the refusal in flight its context\n");

// The private client this module reads is the installed package's, and an
// abandoned compiler's process ends.
{
  const api = openCompiler({ cwd: dir });
  // A snapshot, which an orderly close would release by a request.
  api.updateSnapshot({ openFiles: [join(dir, "iterable.ts")] });
  const child = compilerProcess(api);
  const ended = new Promise<void>((done) => child.once("exit", () => done()));
  writeFileSync(fired, "");
  process.env["TSCERT_RECORD_ALL"] = "1";
  abandonCompiler(api);
  delete process.env["TSCERT_RECORD_ALL"];
  // A timer that keeps the loop running while the exit is awaited: the
  // client leaves its process unreferenced.
  let timer: ReturnType<typeof setTimeout> | undefined;
  const timeout = new Promise<string>((done) => { timer = setTimeout(() => done("timeout"), 10_000); });
  const outcome = await Promise.race([ended.then(() => "ended"), timeout]);
  clearTimeout(timer);
  assert.equal(outcome, "ended", "the abandoned compiler's process ended");
  assert.equal(readFileSync(fired, "utf8"), "", "abandoning sends no request");
  process.stdout.write("an abandoned compiler: its process ends, and no request is sent\n");
}
closeParser();

// unchecked.mts asks a node's type again only after a panic the compiler
// replied, and reports the node uninspected; any other failure ends it.
const unchecked = resolve(import.meta.dirname, "../tools/unchecked.mts");
const project = join(dir, "unchecked");
mkdirSync(project);
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({ compilerOptions: { target: "es2022", module: "preserve",
  moduleResolution: "bundler", noEmit: true, strict: true, skipLibCheck: true, lib: ["es2022"], types: [] }, include: ["*.mts"] }));
writeFileSync(join(project, "one.mts"), "export function twice(n: number): number {\n  return n * 2;\n}\n");
const run = (kind: string, limit: string = ""): SpawnSyncReturns<string> => {
  writeFileSync(fired, "");
  const ran = spawnSync(process.execPath, [unchecked, "--project", project], { encoding: "utf8",
    env: { ...process.env, NODE_OPTIONS: `--import ${new URL("./force-tool-failure.mts", import.meta.url).href}`,
      TSCERT_FORCE_FRAME: "at typesOf \\(", TSCERT_FORCE_KIND: kind, TSCERT_FORCE_LIMIT: limit } });
  assert.ok(present(fired) && readFileSync(fired, "utf8").length > 0, `unchecked.mts (${kind}): the failure was not forced`);
  return ran;
};
const exhausted = run("stack");
assert.notEqual(exhausted.status, 0, "unchecked.mts after a stack exhaustion fails");
assert.match(exhausted.stderr, /Maximum call stack size exceeded/);
const panicked = run("panic");
assert.notEqual(panicked.status, 0, "unchecked.mts after a panic fails");
assert.match(panicked.stdout, /error: .*\[tool failure\]  Checker\.getTypeAtLocation panicked on \d+ nodes from this one, asked again in halves/);
assert.match(panicked.stdout, /error: .*\[tool failure\]  Checker\.getTypeAtLocation panicked on this node/);
// A panic the retry answers is reported all the same.
const answered = run("panic", "1");
assert.notEqual(answered.status, 0, "unchecked.mts after a panic its retry answered fails");
assert.match(answered.stdout, /\[tool failure\]  Checker\.getTypeAtLocation panicked on \d+ nodes from this one, asked again in halves/);
assert.match(answered.stdout, / 0 `uninspected`/);
process.stdout.write("unchecked.mts: a panic is reported where it was asked, retried or not, and a stack exhaustion ends it\n");

// A step killed by a signal, as the verifier is when it aborts on a stack
// overflow, is a tool failure naming the signal and what the step wrote.
assert.throws(() => runStep("/bin/sh", ["-c", "echo 'Stack overflow detected. Aborting.' >&2; kill -ABRT $$"]),
  /^Error: tool failure: sh was killed by SIGABRT: Stack overflow detected\. Aborting\.$/);
process.stdout.write("a step killed by a signal: a tool failure naming it\n");
