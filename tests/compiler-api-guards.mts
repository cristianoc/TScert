// C2, the compiler API's guard table (COMPILER-API.md, "Binding the contract
// to the implementation"), regression evidence for its review: the
// generator's output is the reviewed table (`dev/guard-table.mts --check`),
// and every entry, run under Node on an object of each tag value (a tag
// guard on every number around the tag values), answers exactly its tag
// set, and the same with further arguments and another receiver, as a
// callback receives them.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { compilerApiGuards } from "../tools/compiler-api-guards.mts";
import { hostPackage } from "../tools/compiler-api.mts";

const repository = resolve(import.meta.dirname, "..");
const generated = spawnSync(process.execPath, [join(repository, "dev", "guard-table.mts"), "--check"], { encoding: "utf8" });
assert.equal(generated.status, 0, generated.stdout + generated.stderr);

const root = dirname(createRequire(resolve(repository, "tools/package.json")).resolve(`${hostPackage.name}/package.json`));
const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null;
const entry: unknown = await import(pathToFileURL(join(root, compilerApiGuards.entryModule)).href);
assert.ok(isRecord(entry) && isRecord(entry.SyntaxKind), "the entry point exports SyntaxKind");
const syntaxKind = entry.SyntaxKind;
const value = (name: string): number => {
  const v = syntaxKind[name];
  assert.ok(typeof v === "number", `SyntaxKind.${name}`);
  return v;
};
const tagValues = [...new Set(Object.values(syntaxKind).filter((v): v is number => typeof v === "number"))].sort((a, b) => a - b);
const max = Math.max(...tagValues);
const numbers = [...Array.from({ length: max + 5 }, (_, i) => i - 2), 0.5, -0, Number.NaN];
let calls: number = 0;
const isCallable = (v: unknown): v is (this: unknown, ...args: unknown[]) => unknown => typeof v === "function";
for (const guard of compilerApiGuards.guards) {
  const f: unknown = entry[guard.name];
  assert.ok(isCallable(f), `${guard.name} is exported`);
  const call = (receiver: unknown, args: unknown[]): unknown => f.call(receiver, ...args);
  const tags = new Set(guard.tags.map(value));
  const inputs: [unknown, boolean][] = guard.kind === "node"
    ? tagValues.map((t) => [{ kind: t }, tags.has(t)])
    : numbers.map((n) => [n, tags.has(n)]);
  const other = { kind: -1 };
  for (const [input, expected] of inputs) {
    assert.equal(call(undefined, [input]), expected, `${guard.name}(${JSON.stringify(input)})`);
    assert.equal(call(other, [input, 1, [input]]), expected, `${guard.name} with further arguments and a receiver`);
    calls += 2;
  }
}
console.log(`C2: ${compilerApiGuards.guards.length} guards, ${calls} calls under Node, each answering exactly its tag set; ` +
  `${compilerApiGuards.excluded.length} declared guards outside the contract: ${compilerApiGuards.excluded.map(([n]) => n).join(", ")}`);
