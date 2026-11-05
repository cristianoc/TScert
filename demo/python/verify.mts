// The demo's entry point: a Python file through its front end (`py_ast.py`,
// then `lower.mts`), then through TScert's own stages: the verifier's
// control-flow lowering, the OCaml producer's claims, the verifier's evidence
// search and its check. It prints the file's outcome, each unit's, and the directory
// holding what the run wrote.
//
// Usage: node demo/python/verify.mts <file.py>

import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { producerBuild, verifierBuild, producerCall, verifierCall } from "../../pipeline/stage-execution.mts";
import { tested } from "../../pipeline/stages.mts";
import { readDiagnostic } from "../../tools/diagnostic.mts";
import { presentObligation } from "../../tools/diagnostic-view.mts";
import type { Ast } from "../../tools/fragment.mts";
import { Lowering, readNode, Unsupported } from "./lower.mts";

const here = import.meta.dirname;

type Run = { status: number | null; stdout: string; stderr: string };
function run(executable: string, args: string[]): Run {
  const ran = spawnSync(executable, args, { encoding: "utf8", maxBuffer: 1 << 26, timeout: 60_000 });
  if (ran.error) throw ran.error;
  return { status: ran.status, stdout: ran.stdout, stderr: ran.stderr };
}

/** A unit's refusal as a reader of the Python file wants it: the verifier's
 * first line, the obligation it names in source terms, and the Python line
 * at its span. The verifier's full diagnostic stays in `search.log`. */
function readable(detail: string, source: string): string {
  const [first = ""] = detail.split("\n");
  const out = [first];
  const record = readDiagnostic(detail);
  const summary = record && presentObligation(record, source).summary;
  if (summary) out.push(`obligation: ${summary}`);
  const at = /at \[(\d+),(\d+)\)/.exec(first);
  if (at) {
    const start = Number(at[1]);
    const lineStart = source.lastIndexOf("\n", start - 1) + 1;
    const lineEnd = source.indexOf("\n", start);
    const line = source.slice(0, start).split("\n").length;
    out.push(`line ${line}: ${source.slice(lineStart, lineEnd < 0 ? undefined : lineEnd).trim()}`);
  }
  return out.join("\n");
}

/** A stage's refusal: its first line starting with `prefix`, or the whole of its error output. */
function refusal(ran: Run, prefix: string): string {
  const line = `${ran.stdout}\n${ran.stderr}`.split("\n").find((l) => l.startsWith(prefix));
  return line ?? `tool failure (exit ${ran.status}): ${ran.stderr.trim()}`;
}

type Report = {
  status: "verified" | "unsupported" | "unverified" | "error";
  artifacts: string;
  detail?: string;
  units?: { unit: string; status: string; detail: string }[];
};

function verify(file: string): Report {
  const artifacts = mkdtempSync(join(tmpdir(), "tscert-python-"));
  const bytes = readFileSync(file);
  const snapshot = join(artifacts, "source.py");
  writeFileSync(snapshot, bytes);
  const parsed = run("python3", ["-I", join(here, "py_ast.py"), snapshot]);
  if (parsed.status !== 0) return { status: "unsupported", artifacts, detail: parsed.stderr.trim() };
  writeFileSync(join(artifacts, "python-ast.json"), parsed.stdout);
  const tree = readNode(JSON.parse(parsed.stdout));
  let fragment: Ast;
  try {
    const sha = createHash("sha256").update(bytes).digest("hex");
    fragment = new Lowering(bytes.toString("utf8")).module(tree, resolve(file), sha);
  } catch (error) {
    if (error instanceof Unsupported) return { status: "unsupported", artifacts, detail: error.message };
    throw error;
  }
  const ast = join(artifacts, "fragment.json");
  writeFileSync(ast, JSON.stringify(fragment));

  const lowered = tested(verifierCall(verifierBuild, ["--lower-control-flow", ast]), 60_000);
  if (lowered.status !== 0) return { status: "unsupported", artifacts, detail: refusal(lowered, "reject: ") };
  const flow = join(artifacts, "flow.json");
  writeFileSync(flow, lowered.stdout);

  const proposed = tested(producerCall(producerBuild, [ast, flow]), 60_000);
  if (proposed.status !== 0) return { status: "unsupported", artifacts, detail: refusal(proposed, "unsupported: ") };
  const claims = join(artifacts, "claims.json");
  writeFileSync(claims, proposed.stdout);

  // The file key names the source; the verifier reads the fragment, not the file.
  const evidence = join(artifacts, "evidence.json");
  const searched = tested(verifierCall(verifierBuild, ["--produce-units", ast, claims, resolve(file), evidence, "12"]), 60_000);
  writeFileSync(join(artifacts, "search.log"), searched.stdout + searched.stderr);
  if (!searched.stdout.includes("checked source evidence written: "))
    return { status: "unverified", artifacts, detail: refusal(searched, "reject: ") };
  const searchRefusals = new Map<string, string>();
  for (const line of searched.stdout.split("\n").filter((l) => l.startsWith("refused: "))) {
    const value: unknown = JSON.parse(line.slice("refused: ".length));
    if (typeof value === "object" && value !== null && "unit" in value && "refusal" in value &&
        typeof value.unit === "string" && typeof value.refusal === "string")
      searchRefusals.set(value.unit, value.refusal);
  }

  const checked = tested(verifierCall(verifierBuild, ["--check-units", ast, claims, resolve(file), evidence]), 60_000);
  writeFileSync(join(artifacts, "check.log"), checked.stdout + checked.stderr);
  const units = checked.stdout.split("\n").filter((l) => l.startsWith("{")).map((line) => {
    const value: unknown = JSON.parse(line);
    if (typeof value !== "object" || value === null || !("unit" in value) || typeof value.unit !== "string")
      throw Error("the verifier printed a verdict without its unit");
    if ("accepted" in value && value.accepted === true) return { unit: value.unit, status: "verified", detail: "" };
    const own = "refusal" in value && typeof value.refusal === "string" ? value.refusal : "";
    return { unit: value.unit, status: "unverified", 
      detail: readable(`reject: ${searchRefusals.get(value.unit) ?? own}`, bytes.toString("utf8")) };
  });
  if (units.length !== fragment.functions.length || new Set(units.map((u) => u.unit)).size !== units.length ||
      (units.every((u) => u.status === "verified") && checked.status !== 0)) return { status: "error", artifacts, detail: refusal(checked, "reject: ") };
  return { status: units.every((u) => u.status === "verified") ? "verified" : "unverified", artifacts, units };
}

const [file] = process.argv.slice(2);
if (file === undefined) {
  process.stderr.write("usage: node demo/python/verify.mts <file.py>\n");
  process.exit(2);
}
const report = verify(file);
process.stdout.write(`${report.status}: ${file}\n`);
for (const u of report.units ?? []) {
  process.stdout.write(`  ${u.status} ${u.unit}\n`);
  for (const line of u.detail.split("\n").filter((l) => l !== "")) process.stdout.write(`    ${line}\n`);
}
if (report.detail !== undefined) process.stdout.write(`  ${report.detail}\n`);
process.stdout.write(`artifacts: ${report.artifacts}\n`);
process.exit(report.status === "verified" ? 0 : 1);
