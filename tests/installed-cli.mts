import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fieldOf } from "../tools/thrown.mts";

const [file] = process.argv.slice(2);
assert.ok(file, "usage: node tests/installed-cli.mts PACKAGE.tgz");
const tarball = resolve(file);
const scratch = mkdtempSync(join(tmpdir(), "tscert-consumer-"));
const cwd = join(scratch, "project");
try {
  mkdirSync(cwd);
  writeFileSync(join(cwd, "package.json"), '{"private":true}\n');
  const installed = spawnSync("npm", ["install", "--no-audit", "--no-fund", "--ignore-scripts", tarball], {
    cwd, stdio: "inherit",
  });
  if (installed.error) throw installed.error;
  assert.equal(installed.status, 0);

  const bin = join(cwd, "node_modules/.bin/tscert");
  const help = spawnSync(bin, ["--help"], { cwd, encoding: "utf8" });
  if (help.error) throw help.error;
  assert.equal(help.status, 0, help.stderr);
  assert.match(help.stdout, /Research preview/);

  writeFileSync(join(cwd, "tsconfig.json"), JSON.stringify({
    compilerOptions: {
      strict: true,
      target: "es2022",
      module: "esnext",
      moduleResolution: "bundler",
      types: ["@cristianoc/tscert/effects"],
    },
    include: ["*.ts"],
  }));
  writeFileSync(join(cwd, "accepted.ts"),
    "export function count(xs: readonly number[]): Modifies<{}, number> { return xs.length; }\n");
  writeFileSync(join(cwd, "refused.ts"),
    "export function wrong(): number { return 'wrong'; }\n");

  function run(args: string[], code: number): string {
    const result = spawnSync(bin, args, {
      cwd, encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: join(scratch, "stage-store"), TMPDIR: scratch },
    });
    if (result.error) throw result.error;
    assert.equal(result.status, code, result.stderr || result.stdout);
    return result.stdout;
  }

  for (const [source, status, code] of [["accepted.ts", "verified", 0], ["refused.ts", "unverified", 1]] as const) {
    const verdict: unknown = JSON.parse(run([source, "--project", "."], code));
    assert.equal(fieldOf(verdict, "status"), status);
    console.log(`installed tscert: ${source} ${status}`);
  }

  function batch(sources: string[], code: number): unknown[] {
    const stdout = run(["--batch", ...sources, "--project", "."], code);
    return stdout.trimEnd().split("\n").map((line): unknown => JSON.parse(line));
  }
  run(["--batch"], 2);
  const sources = ["accepted.ts", "refused.ts", "missing.ts", "accepted.ts"];
  const results = batch(sources, 1);
  assert.deepEqual(results.map((r) => fieldOf(r, "source")), sources);
  assert.deepEqual(results.map((r) => fieldOf(r, "status")), ["verified", "unverified", "error", "verified"]);
  const directories = results.map((r) => fieldOf(r, "artifacts"));
  assert.equal(new Set(directories).size, results.length);
  for (const index of [0, 1, 3]) {
    const artifacts = directories[index];
    assert.ok(typeof artifacts === "string");
    const log = readFileSync(join(artifacts, "invocations.jsonl"), "utf8");
    const attempts = log.trimEnd().split("\n").map((line): unknown => JSON.parse(line));
    const parse = attempts.filter((e) => fieldOf(e, "event") === "end")
      .map((e) => fieldOf(e, "record")).find((r) => fieldOf(r, "stage") === "parse");
    assert.equal(fieldOf(parse, "execution"), "replayed", `warm parse of ${sources[index]}`);
  }

  assert.deepEqual(batch(["accepted.ts"], 0).map((r) => fieldOf(r, "status")), ["verified"]);
  writeFileSync(join(cwd, "accepted.ts"), "export function count(): number { return 'wrong'; }\n");
  assert.deepEqual(batch(["accepted.ts", "refused.ts"], 1).map((r) => fieldOf(r, "status")), ["unverified", "unverified"]);
  console.log("installed tscert: ordered batch verdicts, warm replay and changed source");
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
