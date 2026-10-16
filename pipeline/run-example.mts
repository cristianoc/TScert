// Run a pipeline example as JavaScript: what Node does with the source a case
// checks, for the controls that compare a case's outcome with its execution.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import vm from "node:vm";
// ../tools/strip-types.mts erases the annotations of an example run as JavaScript.
import { stripTypes } from "../tools/strip-types.mts";
const here = import.meta.dirname;
/** An example run as JavaScript, then `expression` evaluated after it. */
export const runExample = (file: string, expression: string): unknown =>
  vm.runInNewContext(`${stripTypes(readFileSync(join(here, "examples", `${file}.ts`), "utf8"))
    .replace(/^export /gm, "")}\n${expression}`, {}, { timeout: 1000 });
/** Run a value-import example as Node runs its ES modules, then print
 * `expression`: the example and the modules of `imports-project` it imports
 * are stripped of types, `@fixture/NAME` resolved to `NAME`'s module. */
export const runImporting = (file: string, expression: string): unknown => {
  const out = mkdtempSync(join(tmpdir(), "imports-"));
  const project = join(here, "imports-project");
  const relink = (text: string): string => stripTypes(text).replace(/from "@fixture\/([\w-]+)"/g, 'from "./$1.mjs"');
  for (const name of ["lib", "relay"])
    writeFileSync(join(out, `${name}.mjs`), relink(readFileSync(join(project, `${name}.ts`), "utf8")));
  writeFileSync(join(out, "main.mjs"), `${relink(readFileSync(join(here, "examples", `${file}.ts`), "utf8"))}
console.log(JSON.stringify(${expression}));
`);
  const run = spawnSync(process.execPath, [join(out, "main.mjs")], { encoding: "utf8", timeout: 30_000 });
  assert.ifError(run.error);
  assert.equal(run.status, 0, run.stderr);
  const printed: unknown = JSON.parse(run.stdout);
  return printed;
};
/** Run an example as TypeScript's own emit compiles it, then `expression`:
 * an enum, which type stripping does not erase, and whose member reads a
 * transforming stripper may replace by their values. TypeScript emits the
 * file whatever errors it reports. */
export const runEmitted = (file: string, expression: string): unknown => {
  const out = mkdtempSync(join(tmpdir(), "emitted-"));
  const tsc = spawnSync(join(here, "..", "tools", "node_modules", ".bin", "tsc"),
    ["--target", "es2022", "--strict", "--outDir", out, join(here, "examples", `${file}.ts`)], { encoding: "utf8", timeout: 60_000 });
  assert.ifError(tsc.error);
  return vm.runInNewContext(`${readFileSync(join(out, `${file}.js`), "utf8")}\n${expression}`, {}, { timeout: 1000 });
};
