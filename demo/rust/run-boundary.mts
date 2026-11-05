// Optional real Rust -> wasm-bindgen -> TypeScript demonstration. All build
// output, generated declarations, snapshots, hashes and logs stay in tmpdir.
// Requires rustc/cargo, the wasm32 target and wasm-bindgen-cli 0.2.130.
// Usage: WASM_BINDGEN=/path/to/wasm-bindgen node demo/rust/run-boundary.mts
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const here = import.meta.dirname;
const root = mkdtempSync(join(tmpdir(), "tscert-rust-boundary-"));
const rustSource = readFileSync(join(here, "examples/boundary/lib.rs"), "utf8");
const bindgen = process.env["WASM_BINDGEN"] ?? "wasm-bindgen";
const version = "0.2.130";
type Run = { command: string[]; status: number | null; stdout: string; stderr: string };
const runs: Run[] = [];
function run(program: string, args: string[], timeout: number = 240_000): Run {
  const result = spawnSync(program, args, { encoding: "utf8", timeout, maxBuffer: 1 << 26,
    env: { ...process.env, CARGO_TARGET_DIR: join(root, "target") } });
  if (result.error) throw result.error;
  const record = { command: [program, ...args], status: result.status, stdout: result.stdout, stderr: result.stderr };
  runs.push(record);
  writeFileSync(join(root, "commands.json"), JSON.stringify(runs, null, 2));
  return record;
}
function success(program: string, args: string[]): Run {
  const result = run(program, args);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  return result;
}
process.stdout.write(`artifacts: ${root}\n`);
const rustc = success("rustc", ["--version"]);
const cli = success(bindgen, ["--version"]);
assert.equal(cli.stdout.trim(), `wasm-bindgen ${version}`, "CLI and crate must use the pinned matching release");
mkdirSync(join(root, "src"));
writeFileSync(join(root, "src/lib.rs"), rustSource);
writeFileSync(join(root, "package.json"), JSON.stringify({ type: "module" }));
writeFileSync(join(root, "Cargo.toml"), `[package]\nname = "tscert_boundary_demo"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\ncrate-type = ["cdylib"]\n\n[dependencies]\nwasm-bindgen = "=${version}"\n\n[profile.release]\npanic = "abort"\n`);
success("cargo", ["build", "--manifest-path", join(root, "Cargo.toml"), "--target", "wasm32-unknown-unknown", "--release"]);
const generated = join(root, "generated");
success(bindgen, ["--target", "web", "--out-name", "lib", "--out-dir", generated,
  join(root, "target/wasm32-unknown-unknown/release/tscert_boundary_demo.wasm")]);
const fresh = readFileSync(join(generated, "lib.d.ts"), "utf8");
const stale = readFileSync(join(here, "examples/boundary-mismatch/lib.d.ts"), "utf8");
const oldCaller = readFileSync(join(here, "examples/boundary-mismatch/caller.ts"), "utf8");
const fixedCaller = `import { scale } from "./lib.js";\n\nexport function doubled(x: bigint): bigint {\n  return scale(x, 2n);\n}\n`;
const tsc = join(here, "../../tools/node_modules/typescript/lib/tsc.js");
const states = [
  { name: "stale-return", declaration: fresh.replace("next_id(): bigint", "next_id(): number"),
    caller: readFileSync(join(here, "examples/boundary-return-mismatch/caller.ts"), "utf8"),
    tsc: 0, boundary: 1, argument: "none", exported: "jobId" },
  { name: "return-declaration-repaired", declaration: fresh,
    caller: readFileSync(join(here, "examples/boundary-return-mismatch/caller.ts"), "utf8"),
    tsc: 1, boundary: 1, argument: "none", exported: "jobId" },
  { name: "return-repaired", declaration: fresh,
    caller: readFileSync(join(here, "examples/boundary-return/caller.ts"), "utf8"),
    tsc: 0, boundary: 0, argument: "none", exported: "jobId" },
  { name: "stale", declaration: stale, caller: oldCaller, tsc: 0, boundary: 1, argument: "number" },
  { name: "declaration-repaired", declaration: fresh, caller: oldCaller, tsc: 1, boundary: 1, argument: "number" },
  { name: "repaired", declaration: fresh, caller: fixedCaller, tsc: 0, boundary: 0, argument: "bigint" },
];
for (const state of states) {
  const dir = join(root, state.name);
  mkdirSync(dir);
  writeFileSync(join(dir, "lib.rs"), rustSource);
  writeFileSync(join(dir, "lib.d.ts"), state.declaration);
  writeFileSync(join(dir, "lib.js"), 'export * from "../generated/lib.js";\n');
  writeFileSync(join(dir, "caller.ts"), state.caller);
  writeFileSync(join(dir, "tsconfig.json"), readFileSync(join(here, "examples/boundary/tsconfig.json")));
  const typed = run(process.execPath, [tsc, "--project", dir]);
  assert.equal(typed.status === 0, state.tsc === 0, typed.stdout + typed.stderr);
  if (state.tsc !== 0) assert.match(typed.stdout + typed.stderr, /error TS(?:2322|2345)/);
  const boundary = run(process.execPath, [join(here, "verify-boundary.mts"), dir]);
  assert.equal(boundary.status, state.boundary, boundary.stdout + boundary.stderr);
  if (state.name === "stale-return") {
    assert.match(boundary.stdout, /verified jobId@/);
    assert.match(boundary.stdout, /lib.d.ts.*number.*bigint/);
  } else if (state.name === "stale") {
    assert.match(boundary.stdout, /verified doubled@/);
    assert.match(boundary.stdout, /parameter x: lib.d.ts states number; Rust i64 requires bigint/);
  } else if (state.name.endsWith("declaration-repaired")) {
    assert.match(boundary.stdout, /unverified (?:doubled|jobId)@/);
    assert.match(boundary.stdout, /agreed: lib.d.ts against lib.rs/);
  } else assert.match(boundary.stdout, /passed: Rust model, caller and declaration checks/);
  const runtime = success(process.execPath, [join(here, "execute-boundary.mts"), generated, join(dir, "caller.ts"), state.argument, state.exported ?? "doubled"]);
  const result: unknown = JSON.parse(runtime.stdout);
  if (typeof result !== "object" || result === null || !("status" in result)) throw Error(runtime.stdout);
  if (state.argument === "number") {
    assert.equal(result.status, "threw");
    assert.ok("name" in result && result.name === "TypeError");
    assert.ok("message" in result && typeof result.message === "string" && /BigInt/.test(result.message));
  } else {
    assert.equal(result.status, "returned");
    assert.ok("type" in result && result.type === "bigint");
    assert.ok("value" in result && result.value === "42");
  }
  process.stdout.write(`${state.name}: tsc ${typed.status === 0 ? "accepts" : "rejects"}; boundary ${boundary.status === 0 ? "passes" : "refuses"}; runtime ${runtime.stdout.trim()}\n`);
}
const files = ["src/lib.rs", "Cargo.toml", "Cargo.lock", "generated/lib.js", "generated/lib.d.ts", "generated/lib_bg.wasm",
  ...states.flatMap((s) => [`${s.name}/lib.rs`, `${s.name}/lib.d.ts`, `${s.name}/lib.js`, `${s.name}/caller.ts`])];
const hashes = files.map((file) => ({ file, sha256: createHash("sha256").update(readFileSync(join(root, file))).digest("hex") }));
writeFileSync(join(root, "report.json"), JSON.stringify({ node: process.version, rustc: rustc.stdout.trim(), wasmBindgen: cli.stdout.trim(), hashes, runs }, null, 2));
process.stdout.write(`report: ${join(root, "report.json")}\n`);
