// ============================================================================
// PROTOTYPE ONLY — SCHEDULED FOR DELETION UPON UNIFICATION
// Disposable experimental paper-rules prototype (`docs/drafts/paper-rules-mode.md`).
// Must NEVER be imported by `tools/`, `pipeline/`, or `lean/Verification/`
// (enforced by `tests/prototype-isolation.mts`). Replaced upon unification by
// mechanical annotation parsing plus proved CFG checks in `lean/Verification/`.
// ============================================================================

// The experimental prototype of docs/drafts/paper-rules-mode.md over one
// source file: the ordinary check (`pipeline/verify-source.mts`), then the
// paper's annotations (`dev/paper-annotations.mts`) and the pass with the
// rules' layer (`lean/PaperRulesPrototype.lean`, its soundness the axiom
// `paperKeptFactsSurvive`) over the same parsed file. A caller whose written
// instance fails its bound (rule Inst, decided by the annotations script) is
// refused whatever the pass says of it, as is a function the annotations
// script refuses: one whose bound's regions its own steps may change (rule
// Bound's second premise), whose callback's type it does not read, or one
// referenced other than by a call some unit checks.
//   node dev/paper-rules.mts file.ts [--project dir]
//   node dev/paper-rules.mts --check dev/paper-rules/expected.json
// The second form runs every file the expectations list, with their
// directory as the project, and fails on any verdict that differs.
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { check, sourceKey } from "../pipeline/verify-source.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { annotations } from "./paper-annotations.mts";

const prototype = resolve(import.meta.dirname, "../lean/.lake/build/bin/paper-rules-prototype");

/** A unit's verdict line from the prototype. */
interface Verdict {
  unit: string; accepted?: boolean; acceptedUnderPaperRules?: boolean; assumed?: string; assumes?: string[]; refusal?: string;
}

function isVerdict(v: unknown): v is Verdict {
  return typeof v === "object" && v !== null && "unit" in v && typeof v.unit === "string";
}

/** A file's verdicts: the ordinary check's status, and each unit's verdict
under the prototype, `accepted` or `refused`, with its text. */
interface Run { ordinary: string; units: Map<string, { kind: "accepted" | "refused"; text: string }> }

function run(file: string, project: string | undefined, quiet: boolean = false): Run {
  const result: Run = { ordinary: "", units: new Map() };
  // The run's directory retained: the prototype reads its parsed file.
  const ordinary = check(file, project === undefined ? undefined : tsconfigOf(project), false, undefined, true,
    { omitted: [], select: null });
  const detail = "detail" in ordinary && typeof ordinary.detail === "string" ? `: ${ordinary.detail.split("\n")[0]?.slice(0, 160) ?? ""}` : "";
  result.ordinary = ordinary.status;
  if (!quiet) process.stdout.write(`ordinary: ${ordinary.status}${detail}\n`);
  const artifacts = ordinary.artifacts;
  const side = annotations(resolve(file));
  const sidePath = join(artifacts, "paper-side.json");
  writeFileSync(sidePath, JSON.stringify(side));
  // The interfaces the ordinary check read: its imports' established module
  // interfaces where it established them, ordinary contracts otherwise.
  const established = join("interfaces", "interfaces.json");
  const interfaces = existsSync(join(artifacts, established)) ? established : join("interfaces", "ordinary-interfaces.json");
  const out = execFileSync(prototype, [sidePath, "fragment.json", interfaces,
    sourceKey(artifacts), "12"], { cwd: artifacts, encoding: "utf8", stdio: ["ignore", "pipe", process.env.PAPER_TRACE ? "inherit" : "ignore"], timeout: 300_000 });
  const failed = new Map([
    ...side.refusals.map((r): [string, string] => [r.unit, r.reason]),
    ...side.calls.filter((c) => !c.ok).map((c): [string, string] => [c.caller, c.reason ?? "instance"]),
    ...side.assumes.filter((a) => !a.ok).map((a): [string, string] => [a.caller, `assume at line ${a.line}: ${a.reason ?? "form"}`]),
  ]);
  for (const line of out.split("\n").filter((l) => l.startsWith("{"))) {
    const parsed: unknown = JSON.parse(line);
    if (!isVerdict(parsed)) continue;
    const name = parsed.unit.split("@")[0] ?? parsed.unit;
    const inst = failed.get(name);
    const verdict = inst !== undefined ? `refused: ${inst}`
      : parsed.acceptedUnderPaperRules ? `accepted under the paper's rules (assumes ${parsed.assumed ?? "?"}` +
          `${(parsed.assumes ?? []).map((a) => `; assumes ${a}`).join("")})`
      : parsed.accepted ? "accepted"
      : `refused: ${(parsed.refusal ?? "").split("\n")[0]?.slice(0, 160)}`;
    result.units.set(name, { kind: verdict.startsWith("refused") ? "refused" : "accepted", text: verdict });
    if (!quiet) process.stdout.write(`prototype: ${name}: ${verdict}\n`);
  }
  return result;
}

/** The expectations: per file, the ordinary check's status and each unit's
 * verdict under the prototype. */
interface Expected { [file: string]: { ordinary: string; units: Record<string, "accepted" | "refused"> } }

function isExpected(v: unknown): v is Expected {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

/** Every listed file against its expectations: a table, and a failing exit on
 * any difference, a missing unit included. */
function checkAll(path: string): void {
  const parsed: unknown = JSON.parse(readFileSync(path, "utf8"));
  if (!isExpected(parsed)) throw new Error(`${path}: an object of files`);
  const dir = dirname(resolve(path));
  let failures = 0;
  for (const [file, want] of Object.entries(parsed)) {
    const got = run(join(dir, file), dir, true);
    const okOrdinary = got.ordinary === want.ordinary;
    if (!okOrdinary) failures++;
    process.stdout.write(`${okOrdinary ? "ok  " : "FAIL"} ${file} (ordinary): expected ${want.ordinary}, got ${got.ordinary}\n`);
    for (const [unit, kind] of Object.entries(want.units)) {
      const actual = got.units.get(unit);
      const ok = actual?.kind === kind;
      if (!ok) failures++;
      process.stdout.write(`${ok ? "ok  " : "FAIL"} ${file} ${unit}: expected ${kind}, got ${actual?.text ?? "no verdict"}\n`);
    }
    for (const unit of got.units.keys())
      if (!(unit in want.units)) { failures++; process.stdout.write(`FAIL ${file} ${unit}: no expectation\n`); }
  }
  process.stdout.write(`${failures === 0 ? "all expectations met" : `${failures} mismatches`}\n`);
  if (failures > 0) process.exitCode = 1;
}

if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const args = process.argv.slice(2);
  const checkAt = args.indexOf("--check");
  const at = args.indexOf("--project");
  const project = at < 0 ? undefined : args.splice(at, 2)[1];
  const file = args[0];
  const expectations = checkAt < 0 ? undefined : args[checkAt + 1];
  if (expectations !== undefined) checkAll(expectations);
  else if (file === undefined) {
    process.stderr.write("usage: node dev/paper-rules.mts file.ts [--project dir]\n");
    process.exitCode = 2;
  } else {
    readFileSync(file);
    run(file, project);
  }
}
