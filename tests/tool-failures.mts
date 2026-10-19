// A failure of the tool is reported as one, never as a refusal, an absence
// or an unknown answer: at each kind of site that catches what a query
// throws, a forced failure (`force-tool-failure.mts`) surfaces as a tool
// failure, and the forcing is checked to have happened there.
import "./force-tool-failure.mts";
import assert from "node:assert/strict";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { close as closeParser, parseFile } from "../tools/fragment-parse.mts";
import { messageOf } from "../tools/thrown.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

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
  assert.ok(readFileSync(fired, "utf8").length > 0, `${name}: the failure was not forced where ${JSON.stringify(force)} says`);
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

// After a tool failure the parser's compiler is released, so the next parse
// reads replies of its own.
writeFileSync(fired, "");
const fresh = parseFile(join(dir, "iterable.ts"), false, config);
assert.ok(fresh.functions.length === 1, "a parse after a tool failure lowers its function");
process.stdout.write("a parse after a tool failure: as without it\n");
closeParser();

// unchecked.mts asks a node's type again only after a panic the compiler
// replied, and reports the node uninspected; any other failure ends it.
const unchecked = resolve(import.meta.dirname, "../tools/unchecked.mts");
const project = join(dir, "unchecked");
mkdirSync(project);
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({ compilerOptions: { target: "es2022", module: "preserve",
  moduleResolution: "bundler", noEmit: true, strict: true, skipLibCheck: true, lib: ["es2022"], types: [] }, include: ["*.mts"] }));
writeFileSync(join(project, "one.mts"), "export function twice(n: number): number {\n  return n * 2;\n}\n");
const run = (kind: string): SpawnSyncReturns<string> => {
  writeFileSync(fired, "");
  const ran = spawnSync(process.execPath, [unchecked, "--project", project], { encoding: "utf8",
    env: { ...process.env, NODE_OPTIONS: `--import ${new URL("./force-tool-failure.mts", import.meta.url).href}`,
      TSCERT_FORCE_FRAME: "at typesOf \\(", TSCERT_FORCE_KIND: kind } });
  assert.ok(existsSync(fired) && readFileSync(fired, "utf8").length > 0, `unchecked.mts (${kind}): the failure was not forced`);
  return ran;
};
const exhausted = run("stack");
assert.notEqual(exhausted.status, 0, "unchecked.mts after a stack exhaustion fails");
assert.match(exhausted.stderr, /Maximum call stack size exceeded/);
const panicked = run("panic");
assert.match(panicked.stdout, /`uninspected`/);
assert.doesNotMatch(panicked.stdout, / 0 `uninspected`/, "unchecked.mts after a panic reports the nodes uninspected");
process.stdout.write("unchecked.mts: a panic leaves its nodes uninspected, a stack exhaustion ends it\n");
