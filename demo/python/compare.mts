// Reproduce the measured comparison with pinned releases; requires uv/network.
// The report retains commands, versions, outputs and source hashes in tmpdir.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const here = import.meta.dirname;
const artifacts = mkdtempSync(join(tmpdir(), "tscert-python-comparison-"));
const names = ["stale_title", "aliased_arguments", "snapshot_title", "rechecked_title"];
const files = names.map((name) => join(here, "examples", `${name}.py`));
const config = join(artifacts, "pyrightconfig.json");
writeFileSync(config, JSON.stringify({ typeCheckingMode: "strict", pythonVersion: "3.13" }));
const control = join(artifacts, "ordinary_error.py");
writeFileSync(control, "def ordinary_error() -> str:\n    return 0\n");
const tools: { name: string; version: string; options: string[] }[] = [
  { name: "mypy", version: "2.4.1", options: ["--strict", "--no-incremental", "--cache-dir", join(artifacts, "mypy-cache")] },
  { name: "pyright", version: "1.1.414", options: ["--project", config] },
  { name: "basedpyright", version: "1.40.2", options: ["--project", config] },
  { name: "ty", version: "0.0.98", options: ["check"] },
  { name: "pyrefly", version: "1.4.1", options: ["check", "--preset", "strict"] },
];
const runs: { command: string[]; status: number | null; stdout: string; stderr: string }[] = [];
function run(args: string[]): (typeof runs)[number] {
  const result = spawnSync("uv", ["tool", "run", ...args], { cwd: artifacts, encoding: "utf8", timeout: 180_000 });
  if (result.error) throw result.error;
  const record = { command: ["uv", "tool", "run", ...args], status: result.status,
    stdout: result.stdout, stderr: result.stderr };
  runs.push(record);
  writeFileSync(join(artifacts, "report.json"), JSON.stringify({
    sources: files.map((file) => ({ file, sha256: createHash("sha256").update(readFileSync(file)).digest("hex") })), runs,
  }, null, 2));
  return record;
}
process.stdout.write(`artifacts: ${artifacts}\n`);
for (const tool of tools) {
  const prefix = ["--from", `${tool.name}==${tool.version}`, tool.name];
  const version = run([...prefix, "--version"]);
  assert.equal(version.status, 0, version.stderr);
  const good = run([...prefix, ...tool.options, ...files]);
  assert.equal(good.status, 0, good.stdout + good.stderr);
  const bad = run([...prefix, ...tool.options, control]);
  assert.equal(bad.status, 1, `${tool.name}: expected an ordinary type-error exit`);
  assert.match(bad.stdout + bad.stderr, /ordinary_error\.py/);
  assert.match(bad.stdout + bad.stderr, /return|Return|incompatible|assignable/i);
  process.stdout.write(`${version.stdout.trim()}: accepts both aliasing bugs and both repairs; rejects ordinary return error\n`);
}
