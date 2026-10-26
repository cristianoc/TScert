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
import { runDirectory, keepRunDirectories, ownedRun, withinRunDirectory } from "./run-directory.mts";

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

type DiagnosticScope = { name: string; pos: Span; references: Set<string> };

/** All strings are conservative possible references, including closure captures.
 * Unlocated and module-level regions retain document scope. */
function diagnosticScopes(ast: Record<string, unknown>): DiagnosticScope[] {
  return list(ast.functions).map(raw => {
    const fn = object(raw);
    const namePos = span(fn.namePos);
    const scope: DiagnosticScope = { name: string(fn.name), pos: [...namePos], references: new Set() };
    const visit = (value: unknown): void => {
      if (typeof value === "string") scope.references.add(value);
      else if (Array.isArray(value)) for (const item of value) visit(item);
      else if (value && typeof value === "object") {
        for (const [key, item] of Object.entries(value)) {
          if (key === "pos" || key === "namePos") {
            const at = span(item);
            scope.pos[1] = Math.max(scope.pos[1], at[1]);
          } else visit(item);
        }
      }
    };
    visit(fn);
    return scope;
  });
}

function attribute(report: DiagnosticReport, scopes: DiagnosticScope[]): void {
  const owner = (pos: Span): DiagnosticScope | undefined => scopes.find(s =>
    s.pos[0] <= pos[0] && pos[1] <= s.pos[1]);
  const reach = new Map<DiagnosticScope, Set<DiagnosticScope>>();
  for (const scope of scopes) {
    const seen = new Set([scope]);
    for (const next of seen) for (const candidate of scopes)
      if (next.references.has(candidate.name)) seen.add(candidate);
    reach.set(scope, seen);
  }
  const previous = new Map<DiagnosticScope | undefined, string>();
  for (const occurrence of report.occurrences) {
    const scope = owner(occurrence.pos);
    const dependencies = [...previous].filter(([prior]) =>
      !scope || !prior || reach.get(scope)?.has(prior)).map(([, id]) => id);
    if (occurrence.conditional && (occurrence.layer === "search" || occurrence.layer === "check"))
      dependencies.push("supplied-interfaces");
    occurrence.dependencies = dependencies;
    occurrence.conditional ||= dependencies.length > 0;
    if (["source", "planning", "proposal", "extraction"].includes(occurrence.layer)) previous.set(scope, occurrence.id);
  }
}

/** One source run, with one invocation of each applicable stage. */
export function diagnose(source: string, project?: string, retainArtifacts: boolean = false): DiagnosticReport & Disposable {
  const file = resolve(source);
  const bytes = readFileSync(file);
  const artifacts = runDirectory("diagnostic-");
  using directoryScope = withinRunDirectory(artifacts);
  const recorder = new Recorder(join(artifacts, invocationLog));
  const report: DiagnosticReport = { status: "diagnostic", source: file,
    sourceSha256: createHash("sha256").update(bytes).digest("hex"), artifacts,
    attempted: 0, completed: false, occurrences: [], unexamined: [], error: null };
  const whole: Span = [0, bytes.toString("utf8").length];
  let scopes: DiagnosticScope[] = [];
  const add = (layer: string, pos: Span, reason: string, conditional: boolean): void => {
    const located = /at \[(\d+),(\d+)\)/.exec(reason);
    if (located) pos = [Number(located[1]), Number(located[2])];
    else if (pos[0] === 0 && pos[1] === 0) pos = whole;
    const dependencies: string[] = [];
    const id = `refusal:${report.occurrences.length}`;
    report.occurrences.push({ id, layer, pos, reason,
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
      scopes = diagnosticScopes(ast);
      if (ast.sourceSha256 !== report.sourceSha256) throw Error("diagnostic source fingerprint differs");
      const fragment = join(artifacts, "diagnostic-fragment.json");
      writeFileSync(fragment, parsed.out);
      const flow = step(verifierCall(verifier, ["--diagnostic-control-flow", fragment]), "planning");
      if (flow !== null) {
        const flowPath = join(artifacts, "diagnostic-flow.json");
        const planned = object(JSON.parse(flow));
        for (const raw of list(planned.occurrences)) {
          const occurrence = object(raw);
          const pos = span(occurrence.pos);
          add("planning", pos, string(occurrence.reason), true);
          report.unexamined.push({ pos, reason: "opaque planning expression replaced by undefined" });
        }
        writeFileSync(fragment, JSON.stringify({ ...envelope, diagnostic: planned.diagnostic }));
        writeFileSync(flowPath, JSON.stringify(list(planned.graph)));
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
            ["--diagnose-source-claims-local", fragment, claims, file, "12"]), "extraction");
          if (searched !== null) {
            let result = object(JSON.parse(searched));
            if (result.status !== "diagnostic" || typeof result.attempted !== "number") throw Error("invalid diagnostic result");
            const traversed = result.attempted;
            if (result.completed !== true && traversed > 0) {
              try {
                const retried = step(verifierCall(verifier,
                  ["--diagnose-source-claims", fragment, claims, file, "12"]), "aggregate");
                if (retried !== null) {
                  const checked = object(JSON.parse(retried));
                  if (checked.status !== "diagnostic" || typeof checked.attempted !== "number")
                    throw Error("invalid diagnostic completion result");
                  result = checked;
                }
              } catch (error) {
                report.error = `diagnostic aggregate retry failed: ${String(error)}`;
                add("aggregate", whole, report.error, true);
                report.unexamined.push({ pos: whole, reason: report.error });
              }
            }
            if (typeof result.attempted !== "number") throw Error("invalid diagnostic attempt count");
            report.attempted = traversed;
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
  try {
    attribute(report, scopes);
    writeFileSync(join(artifacts, "diagnostic.json"), JSON.stringify(report, null, 2) + "\n");
  } catch (error) {
    // A report that cannot be written releases its run before the failure
    // propagates, as a written one not retained does.
    ownedRun(report, false);
    throw error;
  }
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
