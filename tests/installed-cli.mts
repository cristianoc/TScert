import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fieldOf } from "../tools/thrown.mts";

const [file] = process.argv.slice(2);
assert.ok(file, "usage: node tests/installed-cli.mts PACKAGE.tgz");
const tarball = resolve(file);
const cwd = mkdtempSync(join(tmpdir(), "tscert-consumer-"));
try {
  writeFileSync(join(cwd, "package.json"), '{"private":true}\n');
  const installed = spawnSync("npm", ["install", "--no-audit", "--no-fund", "--ignore-scripts", tarball], {
    cwd, stdio: "inherit",
  });
  if (installed.error) throw installed.error;
  assert.equal(installed.status, 0);

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

  for (const [source, status, code] of [["accepted.ts", "verified", 0], ["refused.ts", "unverified", 1]] as const) {
    const result = spawnSync(join(cwd, "node_modules/.bin/tscert"), [source, "--project", "."], {
      cwd, encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: join(cwd, "stage-store"), TMPDIR: cwd },
    });
    if (result.error) throw result.error;
    assert.equal(result.status, code, result.stderr || result.stdout);
    const verdict: unknown = JSON.parse(result.stdout);
    assert.equal(fieldOf(verdict, "status"), status, result.stdout);
    console.log(`installed tscert: ${source} ${status}`);
  }
} finally {
  rmSync(cwd, { recursive: true, force: true });
}
