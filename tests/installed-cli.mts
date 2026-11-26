import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
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

  function run(args: string[], code: number, extraEnv: NodeJS.ProcessEnv = {}): string {
    const result = spawnSync(bin, args, {
      cwd, encoding: "utf8", env: {
        ...process.env, TSCERT_STAGE_STORE: join(scratch, "stage-store"), TMPDIR: scratch, ...extraEnv,
      },
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

  function batch(sources: string[], code: number, extraEnv?: NodeJS.ProcessEnv): unknown[] {
    const stdout = run(["--batch", ...sources, "--project", "."], code, extraEnv);
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
  // A package with a legacy main field leaves a Node resolution unobserved.
  // Resolve it during the first collection so later inputs must use fresh processes.
  const legacy = join(cwd, "node_modules", "retirement-fixture");
  mkdirSync(legacy);
  writeFileSync(join(legacy, "package.json"), '{"main":"index.js"}\n');
  writeFileSync(join(legacy, "index.js"), "export {};\n");

  const trace = join(scratch, "retirement.log");
  const preload = join(scratch, "retire.mjs");
  const installedModule = (name: string): string =>
    JSON.stringify(pathToFileURL(join(cwd, "node_modules", "@cristianoc", "tscert", "tools", name)).href);
  writeFileSync(preload, String.raw`
    import assert from "node:assert/strict";
    import { appendFileSync } from "node:fs";
    import { join } from "node:path";
    import { injectSessionFaultForTests } from ${installedModule("declaration-session.mjs")};
    import { nodeResolve, processRetirement } from ${installedModule("files.mjs")};
    const trace = ${JSON.stringify(trace)};
    const args = process.argv.slice(2);
    if (args[0] === "--batch") {
      appendFileSync(trace, "started " + process.pid + "\n");
      if (args.indexOf("--project") > 2) {
        injectSessionFaultForTests({ kind: "during", during() {
          injectSessionFaultForTests(null);
          nodeResolve("retirement-fixture", join(process.cwd(), "accepted.ts"));
          assert.match(processRetirement() ?? "", /states no exports/);
          appendFileSync(trace, "retired " + process.pid + "\n");
        } });
      }
    }
  `);
  const retirementSources = ["accepted.ts", "refused.ts", "accepted.ts"];
  const afterRetirement = batch(retirementSources, 1, {
    NODE_OPTIONS: [process.env.NODE_OPTIONS, `--import=${pathToFileURL(preload).href}`].filter(Boolean).join(" "),
  });
  assert.deepEqual(afterRetirement.map((r) => fieldOf(r, "source")), retirementSources);
  assert.deepEqual(afterRetirement.map((r) => fieldOf(r, "status")), ["verified", "unverified", "verified"]);
  const [started, retired, ...replacements] = readFileSync(trace, "utf8").trimEnd().split("\n");
  assert.match(started, /^started \d+$/);
  assert.equal(retired, started.replace("started ", "retired "));
  assert.equal(replacements.length, 2);
  for (const replacement of replacements) assert.match(replacement, /^started \d+$/);
  assert.equal(new Set([started, ...replacements]).size, 3, "each remaining source runs in a fresh process");
  console.log("installed tscert: forced batch retirement");

  writeFileSync(join(cwd, "accepted.ts"), "export function count(): number { return 'wrong'; }\n");
  assert.deepEqual(batch(["accepted.ts", "refused.ts"], 1).map((r) => fieldOf(r, "status")), ["unverified", "unverified"]);
  console.log("installed tscert: ordered batch verdicts, warm replay and changed source");
} finally {
  rmSync(scratch, { recursive: true, force: true });
}
