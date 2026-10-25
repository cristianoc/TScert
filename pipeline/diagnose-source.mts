/** Diagnostic inventories are disjoint from the verification outcome and
 * evidence wires. Every recovered region is retained as a hole. */
import { readFileSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { join, resolve } from "node:path";
import type { Span } from "../tools/span.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { diagnosticParseCall } from "./parse-stage.mts";
import { invokeInProcess, Recorder } from "./stages.mts";
import { producerCall, verifierCall } from "./stage-execution.mts";
import { runStep, producerExecutable, verifier, invocationLog, refusalEnd } from "./verify-source.mts";
import { runDirectory, keepRunDirectories, ownedRun } from "./run-directory.mts";

export type Occurrence = {
  id: string;
  layer: string;
  pos: Span;
  reason: string;
  conditional: boolean;
  dependencies: string[];
};
export type DiagnosticReport = {
  status: "diagnostic" | "error";
  source: string;
  sourceSha256: string;
  artifacts: string;
  attempted: number;
  completed: boolean;
  occurrences: Occurrence[];
  unexamined: { pos: Span; reason: string }[];
  error: string | null;
};

function object(value: unknown): Record<string, unknown> {
  if (!value || typeof value !== "object" || Array.isArray(value)) throw Error("expected diagnostic object");
  // asserted: a decoder boundary after excluding null, arrays and nonobjects
  return value as Record<string, unknown>;
}
function list(value: unknown): unknown[] {
  if (!Array.isArray(value)) throw Error("expected diagnostic array");
  return value;
}
function string(value: unknown): string {
  if (typeof value !== "string") throw Error("expected diagnostic text");
  return value;
}
function span(value: unknown): Span {
  const xs = list(value);
  if (xs.length !== 2 || typeof xs[0] !== "number" || typeof xs[1] !== "number" ||
      !Number.isSafeInteger(xs[0]) || !Number.isSafeInteger(xs[1]) || xs[0] < 0 || xs[1] < xs[0])
    throw Error("expected diagnostic span");
  return [xs[0], xs[1]];
}

/** One source run, with one invocation of each applicable stage. */
export function diagnose(source: string, project?: string, retainArtifacts: boolean = false): DiagnosticReport & Disposable {
  const file = resolve(source);
  const bytes = readFileSync(file);
  const artifacts = runDirectory("diagnostic-");
  const recorder = new Recorder(join(artifacts, invocationLog));
  const report: DiagnosticReport = { status: "diagnostic", source: file,
    sourceSha256: createHash("sha256").update(bytes).digest("hex"), artifacts,
    attempted: 0, completed: false, occurrences: [], unexamined: [], error: null };
  const whole: Span = [0, bytes.toString("utf8").length];
  const add = (layer: string, pos: Span, reason: string, conditional: boolean): void => {
    if (pos[0] === 0 && pos[1] === 0) {
      const located = /at \[(\d+),(\d+)\)/.exec(reason);
      pos = located ? [Number(located[1]), Number(located[2])] : whole;
    }
    const dependencies = report.occurrences.filter(o => o.layer === "source" || o.layer === "proposal").map(o => o.id);
    if (conditional && layer === "search") dependencies.push("supplied-interfaces");
    report.occurrences.push({ id: `refusal:${report.occurrences.length}`, layer, pos, reason,
      conditional: conditional || dependencies.length > 0, dependencies });
  };
  const step = (call: ReturnType<typeof verifierCall>, layer: string): string | null => {
    const ran = runStep(call, recorder);
    if (ran.code === 0) return ran.out;
    const lines = ran.detail.split("\n");
    if (![1, 2].includes(ran.code) || lines.at(-1) !== refusalEnd ||
        !/^(reject|unsupported): /.test(ran.detail)) throw Error(`tool failure: ${ran.detail}`);
    add(layer, whole, lines.slice(0, -1).join("\n"), report.occurrences.length > 0);
    report.unexamined.push({ pos: whole, reason: `${layer} did not produce a document` });
    return null;
  };
  try {
    const parsed = invokeInProcess(diagnosticParseCall(bytes, file, project ? tsconfigOf(project) : undefined), { force: false, recorder }).value;
    const envelope = object(JSON.parse(parsed.out));
    for (const raw of list(envelope.occurrences)) {
      const occurrence = object(raw);
      add("source", span(occurrence.pos), string(occurrence.reason), report.occurrences.length > 0);
      report.unexamined.push({ pos: span(occurrence.region), reason: string(occurrence.recovery) });
    }
    if (envelope.diagnostic !== null) {
      const ast = object(envelope.diagnostic);
      if (ast.sourceSha256 !== report.sourceSha256) throw Error("diagnostic source fingerprint differs");
      const fragment = join(artifacts, "diagnostic-fragment.json");
      writeFileSync(fragment, parsed.out);
      const flow = step(verifierCall(verifier, ["--diagnostic-control-flow", fragment]), "planning");
      if (flow !== null) {
        const flowPath = join(artifacts, "diagnostic-flow.json");
        writeFileSync(flowPath, flow);
        const proposal = step(producerCall(producerExecutable, ["--diagnose", fragment, flowPath]), "proposal");
        if (proposal !== null) {
          const proposed = object(JSON.parse(proposal));
          for (const raw of list(proposed.occurrences)) {
            const occurrence = object(raw);
            const pos = occurrence.pos === null ? whole : span(occurrence.pos);
            add("proposal", pos, string(occurrence.reason), true);
            report.unexamined.push({ pos, reason: "proposal recovery assumes the expected type, or unknown" });
          }
          const claims = join(artifacts, "diagnostic-proposal.json");
          writeFileSync(claims, proposal);
          const searched = step(verifierCall(verifier,
            ["--diagnose-source-claims", fragment, claims, file, "12"]), "extraction");
          if (searched !== null) {
            const result = object(JSON.parse(searched));
            if (result.status !== "diagnostic" || typeof result.attempted !== "number") throw Error("invalid diagnostic result");
            report.attempted = result.attempted;
            report.completed = result.completed === true;
            for (const raw of list(result.occurrences)) {
              const occurrence = object(raw);
              add(string(occurrence.layer), span(occurrence.pos), string(occurrence.reason), occurrence.conditional === true);
            }
            for (const raw of list(result.unexamined)) {
              const region = object(raw);
              const pos = span(region.pos);
              report.unexamined.push({ pos: pos[0] === 0 && pos[1] === 0 ? whole : pos, reason: string(region.reason) });
            }
          }
        }
      }
    }
  } catch (error) {
    report.status = "error";
    report.completed = false;
    report.error = String(error);
    report.unexamined.push({ pos: whole, reason: report.error });
  }
  writeFileSync(join(artifacts, "diagnostic.json"), JSON.stringify(report, null, 2) + "\n");
  return ownedRun(report, retainArtifacts);
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const [source, project] = process.argv.slice(2);
  if (!source) throw Error("usage: diagnose-source.mts source.ts [project]");
  keepRunDirectories();
  const report = diagnose(source, project);
  process.stdout.write(JSON.stringify(report, null, 2) + "\n");
  if (report.status === "error") process.exitCode = 1;
}
