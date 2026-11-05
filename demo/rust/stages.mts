// A Rust crate through the demo's front end (`parse.mts`, then `lower.mts`),
// then through TScert's own stages: the verifier's control-flow lowering,
// the OCaml producer's claims, the verifier's evidence search and its check.
// It calls the stages directly, without the stage store.

import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { producerBuild, verifierBuild } from "../../pipeline/stage-execution.mts";
import { readDiagnostic } from "../../tools/diagnostic.mts";
import { presentObligation } from "../../tools/diagnostic-view.mts";
import type { Ast } from "../../tools/fragment.mts";
import { Lowering } from "./lower.mts";
import { lineOf, Parser, Unsupported, type RCrate } from "./parse.mts";

type Run = { status: number | null; stdout: string; stderr: string };
function run(executable: string, args: string[]): Run {
  const ran = spawnSync(executable, args, { encoding: "utf8", maxBuffer: 1 << 30 });
  if (ran.error) throw ran.error;
  return { status: ran.status, stdout: ran.stdout, stderr: ran.stderr };
}

/** A unit's refusal as a reader of the source wants it: the verifier's
 * first line, the obligation it names in source terms, and the source line at
 * its span. The verifier's full diagnostic stays in `search.log`. */
export function readable(detail: string, source: string): string {
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
    out.push(`line ${lineOf(source, start)}: ${source.slice(lineStart, lineEnd < 0 ? undefined : lineEnd).trim()}`);
  }
  return out.join("\n");
}

/** A stage's refusal: its first line starting with `prefix`, or the whole of its error output. */
function refusal(ran: Run, prefix: string): string {
  const line = `${ran.stdout}\n${ran.stderr}`.split("\n").find((l) => l.startsWith(prefix));
  return line ?? `tool failure (exit ${ran.status}): ${ran.stderr.trim()}`;
}

export type Report = {
  status: "verified" | "unsupported" | "unverified" | "error";
  artifacts: string;
  detail?: string;
  units?: { unit: string; status: string; detail: string }[];
};

/** The file's crate and its lowering, or the front end's refusal. */
export function front(file: string): { source: string; crate: RCrate; lowering: Lowering; fragment: Ast } | { refused: string } {
  const bytes = readFileSync(file);
  const source = bytes.toString("utf8");
  try {
    const crate = new Parser(source).crate();
    const lowering = new Lowering(source, crate);
    const sha = createHash("sha256").update(bytes).digest("hex");
    return { source, crate, lowering, fragment: lowering.crate(crate, resolve(file), sha) };
  } catch (error) {
    if (error instanceof Unsupported) return { refused: error.message };
    throw error;
  }
}

/** A lowered crate through the four stages. */
export function check(file: string, source: string, fragment: Ast): Report {
  const artifacts = mkdtempSync(join(tmpdir(), "tscert-rust-"));
  const ast = join(artifacts, "fragment.json");
  writeFileSync(ast, JSON.stringify(fragment));

  const lowered = run(verifierBuild, ["--lower-control-flow", ast]);
  if (lowered.status !== 0) return { status: "unsupported", artifacts, detail: refusal(lowered, "reject: ") };
  const flow = join(artifacts, "flow.json");
  writeFileSync(flow, lowered.stdout);

  const proposed = run(producerBuild, [ast, flow]);
  if (proposed.status !== 0) return { status: "unsupported", artifacts, detail: refusal(proposed, "unsupported: ") };
  const claims = join(artifacts, "claims.json");
  writeFileSync(claims, proposed.stdout);

  // The file key names the source; the verifier reads the fragment, not the file.
  const evidence = join(artifacts, "evidence.json");
  const searched = run(verifierBuild, ["--produce-units", ast, claims, resolve(file), evidence, "12"]);
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

  const checked = run(verifierBuild, ["--check-units", ast, claims, resolve(file), evidence]);
  writeFileSync(join(artifacts, "check.log"), checked.stdout + checked.stderr);
  const units = checked.stdout.split("\n").filter((l) => l.startsWith("{")).map((line) => {
    const value: unknown = JSON.parse(line);
    if (typeof value !== "object" || value === null || !("unit" in value) || typeof value.unit !== "string")
      throw Error("the verifier printed a verdict without its unit");
    if ("accepted" in value && value.accepted === true) return { unit: value.unit, status: "verified", detail: "" };
    const own = "refusal" in value && typeof value.refusal === "string" ? value.refusal : "";
    return { unit: value.unit, status: "unverified", detail: readable(`reject: ${searchRefusals.get(value.unit) ?? own}`, source) };
  });
  if (units.length === 0) return { status: "error", artifacts, detail: refusal(checked, "reject: ") };
  return { status: units.every((u) => u.status === "verified") ? "verified" : "unverified", artifacts, units };
}

/** Prints a report under `heading`, its units indented. */
export function print(heading: string, report: Report): void {
  process.stdout.write(`${report.status}: ${heading}\n`);
  for (const u of report.units ?? []) {
    process.stdout.write(`  ${u.status} ${u.unit}\n`);
    for (const line of u.detail.split("\n").filter((l) => l !== "")) process.stdout.write(`    ${line}\n`);
  }
  if (report.detail !== undefined) process.stdout.write(`  ${report.detail}\n`);
  process.stdout.write(`  artifacts: ${report.artifacts}\n`);
}
