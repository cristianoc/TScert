// Standalone source-bound assembly controls; no TypeScript compiler channel.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cpSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { ordinaryEffect } from "../../tools/type-graph.mts";
import type { Ast } from "../../tools/fragment.mts";
import { check, front } from "./stages.mts";

const file = join(import.meta.dirname, "examples/rust-i64-calls.rs");
const source = front(file);
assert.ok(!("refused" in source));
const fragment = source.fragment;
const rust = check(file, source.source, fragment);
assert.equal(rust.status, "verified", JSON.stringify(rust));

// A standalone importer Fragment uses the same ordinary source syntax as a
// TypeScript function calling identity. Its declaration supplies the import.
function importer(result: "bigint" | "number"): Ast {
  const ast = structuredClone(fragment);
  const forward = ast.functions.find(f => f.name === "forward");
  assert.ok(forward);
  const span = forward.namePos;
  forward.retType = { k: "atom", name: result, span };
  ast.functions = [forward];
  ast.declarations.values = [{
    binding: { local: "identity", imported: "identity", specifier: "./lib.js", span },
    declaration: { module: "./lib.d.ts", name: "identity", span },
    construct: false, typeParams: [],
    type: { k: "function", receiver: null, rest: null, span, effect: ordinaryEffect,
      params: [{ k: "atom", name: "bigint", span }], result: { k: "atom", name: result, span } },
  }];
  return ast;
}

const honest = check(file, source.source, importer("bigint"));
const stale = check(file, source.source, importer("number"));
assert.equal(honest.status, "verified", JSON.stringify(honest));
assert.equal(stale.status, "verified", JSON.stringify(stale));
const run = (name: string, rustDirectory: string, callerDirectory: string, expected: number): void => {
  const checked = spawnSync(join(import.meta.dirname, "../../lean/.lake/build/bin/boundary-check"),
    [rustDirectory, callerDirectory], { encoding: "utf8", timeout: 60_000 });
  assert.equal(checked.status, expected, `${name}: ${checked.error?.message ?? checked.stderr}`);
  if (expected === 0) assert.equal(checked.stdout.trim(), "linked");
  process.stdout.write(`${name}: ${expected === 0 ? "linked" : "refused"}\n`);
};
run("matching-with-same-module-capture", rust.artifacts, honest.artifacts, 0);
const boundaryFile = join(import.meta.dirname, "examples/boundary/lib.rs");
const boundarySource = front(boundaryFile);
assert.ok(!("refused" in boundarySource));
const boundary = check(boundaryFile, boundarySource.source, boundarySource.fragment);
assert.equal(boundary.status, "verified", JSON.stringify(boundary));
run("full-boundary-including-arithmetic-helpers", boundary.artifacts, honest.artifacts, 0);
run("independently-accepted-stale-result", rust.artifacts, stale.artifacts, 1);

const forged = mkdtempSync(join(tmpdir(), "tscert-linked-forgeries-"));
function forge(name: string, base: string, mutate: (ast: Ast) => void): string {
  const directory = join(forged, name);
  cpSync(base, directory, { recursive: true });
  const ast = structuredClone(fragment);
  mutate(ast);
  writeFileSync(join(directory, "fragment.json"), JSON.stringify(ast));
  return directory;
}
const signature = forge("export-signature", rust.artifacts, ast => {
  const fn = ast.functions.find(f => f.name === "identity");
  assert.ok(fn);
  fn.retType = { k: "atom", name: "string", span: fn.namePos };
});
run("forged-export-signature-honest-evidence", signature, honest.artifacts, 1);
const capture = forge("capture-target", rust.artifacts, ast => {
  const target = ast.functions.find(f => f.name === "text");
  const identity = ast.functions.find(f => f.name === "identity");
  assert.ok(target && identity);
  [target.name, identity.name] = [identity.name, target.name];
});
run("forged-source-capture-target", capture, honest.artifacts, 1);
const missingEvidence = join(forged, "missing-evidence");
cpSync(rust.artifacts, missingEvidence, { recursive: true });
const lines = readFileSync(join(missingEvidence, "evidence.json"), "utf8").trim().split("\n");
writeFileSync(join(missingEvidence, "evidence.json"), lines.slice(1).join("\n") + "\n");
run("missing-export-acceptance", missingEvidence, honest.artifacts, 1);
process.stdout.write(`artifacts: ${forged}\n`);
