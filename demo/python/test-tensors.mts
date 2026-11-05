// End-to-end rank experiment and a forged producer claim, at the Python source and native-contract boundary.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { decodeSourceClaims } from "../../tools/source-claims.mts";
import type { Json } from "../../tools/calculus.mts";
import { tested } from "../../pipeline/stages.mts";
import { verifierBuild, verifierCall } from "../../pipeline/stage-execution.mts";
const here = import.meta.dirname;
const sources = join(here, "examples", "tensors");
const evidenceRoot = mkdtempSync(join(tmpdir(), "tscert-tensor-test-"));
const cases: [string, "verified" | "unverified"][] = [
  ["bad_errors", "unverified"], ["fixed_errors", "verified"],
  ["batch_squeeze", "unverified"], ["fixed_squeeze", "verified"],
  ["unchecked_squeeze", "unverified"], ["scalar_loss", "verified"], ["fixed_loss", "verified"],
];
const runs: { name: string; status: number | null; output: string; artifacts: string; sha256: string }[] = [];
for (const [name, expected] of cases) {
  const file = join(sources, `${name}.py`);
  const run = spawnSync(process.execPath, [join(here, "verify.mts"), "--tensors", file], { encoding: "utf8", timeout: 90_000 });
  if (run.error) throw run.error;
  const output = run.stdout + run.stderr;
  assert.equal(run.status, expected === "verified" ? 0 : 1, output);
  assert.ok(run.stdout.startsWith(`${expected}: `), output);
  if (expected === "unverified") assert.match(output, /source expression obligation/);
  if (name === "batch_squeeze") assert.match(output, /rank 0 \(scalar\) or rank 1 \(vector\).*requires rank 1/);
  if (name === "bad_errors") assert.match(output, /rank 2 \(matrix\).*requires rank 1/);
  const artifacts = /^artifacts: (.+)$/m.exec(run.stdout)?.[1];
  assert.ok(artifacts, output);
  runs.push({ name, status: run.status, output, artifacts,
    sha256: createHash("sha256").update(readFileSync(file)).digest("hex") });
  writeFileSync(join(evidenceRoot, "model-report.json"), JSON.stringify({ runs }, null, 2));
  process.stdout.write(`${name}: ${expected}\n`);
}
// An annotation the front end cannot represent is refused as a whole.
const fixture = readFileSync(join(sources, "fixed_squeeze.py"), "utf8");
for (const [name, source] of [
  ["truthiness", fixture.replace("    return predictions.squeeze(-1)", "    if predictions:\n        return predictions.squeeze(-1)\n    return predictions")],
  ["in-place", fixture.replace("squeeze(-1)", "squeeze_(-1)")],
  ["unimported-contract", fixture.replace("Column, Vector", "Column")],
  ["rebound-contract", fixture.replace("def predict_vector", "def Vector")],
  ["shape-contract", fixture.replace("-> Vector:", "-> Vector[2]:")],
]) {
  const file = join(evidenceRoot, `${name}.py`);
  writeFileSync(file, source);
  const run = spawnSync(process.execPath, [join(here, "verify.mts"), "--tensors", file], { encoding: "utf8", timeout: 90_000 });
  assert.equal(run.status, 1, run.stdout + run.stderr);
  assert.ok(run.stdout.startsWith("unsupported:"), run.stdout + run.stderr);
}
const bad = runs.find((r) => r.name === "batch_squeeze");
assert.ok(bad);
const parsed: Json = JSON.parse(readFileSync(join(bad.artifacts, "claims.json"), "utf8"));
const claims = decodeSourceClaims(parsed);
const fn = claims.functions[0];
assert.ok(fn);
const source = readFileSync(join(sources, "batch_squeeze.py"), "utf8");
const from = source.indexOf("predictions.squeeze()");
const expression = fn.expressions.find((e) => e.pos[0] === from && e.pos[1] === from + "predictions.squeeze()".length);
assert.ok(expression);
expression.type = fn.result;
const forged = join(evidenceRoot, "forged-squeeze-claims.json");
writeFileSync(forged, JSON.stringify(claims));
const evidence = join(evidenceRoot, "forged-squeeze-evidence.json");
const search = tested(verifierCall(verifierBuild, ["--produce-units", join(bad.artifacts, "fragment.json"), forged,
  join(sources, "batch_squeeze.py"), evidence, "12"]), 60_000);
assert.match(search.stdout + search.stderr, /source expression obligation/);
const check = tested(verifierCall(verifierBuild, ["--check-units", join(bad.artifacts, "fragment.json"), forged,
  join(sources, "batch_squeeze.py"), evidence]), 60_000);
assert.notEqual(check.status, 0);
assert.doesNotMatch(check.stdout, /"accepted":true/);
const forging = { claim: "squeeze() claimed as the declared Vector result", search: search.stdout + search.stderr,
  check: check.stdout + check.stderr, checkStatus: check.status };
writeFileSync(join(evidenceRoot, "model-report.json"), JSON.stringify({ verifierSha256: createHash("sha256").update(readFileSync(verifierBuild)).digest("hex"), runs, forging }, null, 2));
process.stdout.write("forged Vector result for squeeze(): refused in evidence search and final checking\n");
