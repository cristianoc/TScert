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
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { check, sourceKey, stepTimeoutMs } from "../pipeline/verify-source.mts";
import { canonical, verifier, verifierCall, type Canonical } from "../pipeline/stage-execution.mts";
import { invokeProcess } from "../pipeline/stages.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { annotations } from "./paper-annotations.mts";

const prototype = resolve(import.meta.dirname, "../lean/.lake/build/bin/paper-rules-prototype");
let prototypeDigestCache: string | null = null;
function prototypeDigest(): string {
  if (prototypeDigestCache === null) {
    prototypeDigestCache = createHash("sha256").update(readFileSync(prototype)).digest("hex");
  }
  return prototypeDigestCache;
}
const paperInterfaceCacheDir = join(homedir(), ".cache", "tscert", "paper-interfaces");

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

function isCanonical(v: unknown): v is Canonical {
  return v === null || typeof v === "string" || typeof v === "boolean" ||
    (typeof v === "number" && Number.isFinite(v)) ||
    (Array.isArray(v) ? v.every(isCanonical) : typeof v === "object" && Object.values(v).every(isCanonical));
}

function isCanonicalObject(v: Canonical | undefined): v is { readonly [key: string]: Canonical } {
  return v !== undefined && v !== null && typeof v === "object" && !Array.isArray(v);
}

function isCanonicalArray(v: Canonical | undefined): v is readonly Canonical[] {
  return Array.isArray(v);
}

function parseCanonical(text: string): Canonical | null {
  const value: unknown = JSON.parse(text);
  return isCanonical(value) ? value : null;
}

/** Whether a decoded module-interface response leaves any requested function
 * unestablished (`established === null`). */
function hasUnestablished(res: Canonical, requestedNames?: readonly Canonical[]): boolean {
  if (!isCanonicalObject(res) || !isCanonicalArray(res.modules)) return true;
  const wantedByLoc = new Map<string, Set<string>>();
  if (requestedNames !== undefined) {
    for (const rn of requestedNames) {
      if (!isCanonicalObject(rn) || typeof rn.location !== "string" || !isCanonicalArray(rn.names)) continue;
      wantedByLoc.set(rn.location, new Set(rn.names.filter((n): n is string => typeof n === "string")));
    }
  }
  for (const row of res.modules) {
    if (!isCanonicalObject(row) || !isCanonicalArray(row.entries)) continue;
    const mod = isCanonicalObject(row.module) && typeof row.module.location === "string" ? row.module.location : "";
    const wanted = wantedByLoc.get(mod);
    for (const e of row.entries) {
      if (!isCanonicalObject(e) || typeof e.name !== "string") continue;
      if (wanted !== undefined && !wanted.has(e.name)) continue;
      if (e.established === null) return true;
    }
  }
  return false;
}

/** Establish imported module interfaces under the paper's rules when the
 * ordinary check could not establish them (e.g. a dependency that itself needs
 * the paper's rules, such as prepare.ts). Each component tries the ordinary
 * verifier first (reusing the stage store cache), falling back to
 * `paper-rules-prototype --module-interface` only when the ordinary interface
 * fails or leaves a requested export unestablished and the dependency's paper
 * annotations have no refusals, bad calls, or unsafe assumes. */
function resolvePaperInterfaces(artifacts: string, project: string | undefined): string | null {
  const work = join(artifacts, "paper-interfaces");
  mkdirSync(work, { recursive: true });
  const selectionPath = join(work, "selection.json");
  writeFileSync(selectionPath, canonical({ names: null, imports: [], functions: [], own: [] }));
  const trace = (msg: string): void => { if (process.env.PAPER_TRACE) process.stderr.write(`resolvePaperInterfaces: ${msg}\n`); };
  const planRun = invokeProcess(
    verifierCall(verifier, ["--subtype-rounds", "100", "--module-interface-plan", join(artifacts, "fragment.json"), selectionPath]),
    { limitMs: stepTimeoutMs, force: false, recorder: null },
  );
  if (planRun.status !== 0) { trace(`plan failed status=${planRun.status} stderr=${planRun.stderr.slice(0, 200)}`); return null; }
  const planJson = parseCanonical(planRun.stdout);
  if (!isCanonicalObject(planJson) || !isCanonicalArray(planJson.components) || planJson.components.length === 0) { trace(`empty/bad plan`); return null; }
  const byModule = new Map<string, { key: string; interface: Canonical }>();
  const projections: Canonical[] = [];
  for (const [index, raw] of planJson.components.entries()) {
    if (!isCanonicalObject(raw) || !isCanonicalArray(raw.modules) || !isCanonicalArray(raw.names) || !isCanonicalArray(raw.dependencies)) return null;
    const members: string[] = [];
    const docFiles = new Map<string, string>();
    for (const m of raw.modules) {
      if (!isCanonicalObject(m) || typeof m.location !== "string") return null;
      members.push(m.location);
      if (isCanonicalObject(m.document) && typeof m.document.file === "string") {
        docFiles.set(m.location, m.document.file);
      }
    }
    const dependencies: { key: string; interface: Canonical }[] = [];
    for (const depLoc of raw.dependencies) {
      if (typeof depLoc !== "string") return null;
      const dep = byModule.get(depLoc);
      if (dep === undefined) return null;
      if (!dependencies.includes(dep)) dependencies.push(dep);
    }
    const reqPath = join(work, `component-${index}.json`);
    writeFileSync(reqPath, canonical({
      modules: raw.modules,
      names: raw.names,
      dependencies,
      force: [],
      fuel: 12,
      mode: 8,
    }));
    let stdout: string | null = null;
    let depKey = "paper-rules-interface";
    const ordRun = invokeProcess(
      verifierCall(verifier, ["--subtype-rounds", "100", "--module-interface", reqPath]),
      { limitMs: stepTimeoutMs, force: false, recorder: null },
    );
    const ordParsed = ordRun.status === 0 ? parseCanonical(ordRun.stdout) : null;
    const baseDir = project !== undefined ? resolve(project) : process.cwd();
    const depSides = members.map((loc) => {
      const depPath = resolve(baseDir, loc);
      return { loc, side: existsSync(depPath) ? annotations(depPath) : null };
    });
    const needsPaperCheck = depSides.some(({ side }) =>
      side !== null && (side.refusals.length > 0 || side.calls.some((c) => !c.ok) || side.assumes.length > 0 ||
        Object.values(side.functions).some((f) => (f.denseWrites?.length ?? 0) > 0)),
    );
    if (ordParsed !== null && !hasUnestablished(ordParsed, raw.names) && !needsPaperCheck) {
      stdout = ordRun.stdout;
      depKey = ordRun.record.key ?? "executed-without-replay";
    } else {
      const sideMap: Record<string, unknown> = {};
      for (const { loc, side } of depSides) {
        const depSide = side ?? annotations(resolve(baseDir, loc));
        if (depSide.refusals.length > 0 || depSide.calls.some((c) => !c.ok) || depSide.assumes.length > 0) {
          trace(`refused annotations for ${loc}`);
          return null;
        }
        sideMap[loc] = depSide;
        const docFile = docFiles.get(loc);
        if (docFile !== undefined && docFile !== loc) sideMap[docFile] = depSide;
      }
      const sideMapPath = join(work, `side-map-${index}.json`);
      const sideMapText = JSON.stringify(sideMap);
      writeFileSync(sideMapPath, sideMapText);
      const reqText = readFileSync(reqPath, "utf8");
      const cacheKey = createHash("sha256")
        .update(prototypeDigest()).update("\0")
        .update(reqText).update("\0")
        .update(sideMapText).digest("hex");
      const cachePath = join(paperInterfaceCacheDir, `${cacheKey}.json`);
      if (existsSync(cachePath)) {
        trace(`cache hit for ${members.join(",")}`);
        stdout = readFileSync(cachePath, "utf8");
        depKey = `paper-${cacheKey.slice(0, 16)}`;
      } else {
        trace(`running paper --module-interface for ${members.join(",")}`);
        try {
          stdout = execFileSync(prototype, ["--module-interface", sideMapPath, reqPath], {
            cwd: artifacts,
            encoding: "utf8",
            maxBuffer: 64 * 1024 * 1024,
            stdio: ["ignore", "pipe", process.env.PAPER_TRACE ? "inherit" : "ignore"],
            timeout: stepTimeoutMs,
          });
          const parsedOut = parseCanonical(stdout);
          if (parsedOut !== null && isCanonicalObject(parsedOut) && isCanonicalArray(parsedOut.modules)) {
            mkdirSync(paperInterfaceCacheDir, { recursive: true });
            const tmpPath = `${cachePath}.${process.pid}.tmp`;
            writeFileSync(tmpPath, stdout);
            renameSync(tmpPath, cachePath);
            depKey = `paper-${cacheKey.slice(0, 16)}`;
          }
        } catch (e) {
          trace(`prototype --module-interface failed on ${members.join(",")}: ${e instanceof Error ? e.message.slice(0, 200) : String(e)}`);
          if (ordRun.status === 0) {
            stdout = ordRun.stdout;
            depKey = ordRun.record.key ?? "executed-without-replay";
          } else {
            return null;
          }
        }
      }
    }
    if (stdout === null) { trace(`null stdout on ${members.join(",")}`); return null; }
    const res = parseCanonical(stdout);
    if (!isCanonicalObject(res) || !isCanonicalArray(res.modules)) { trace(`bad json on ${members.join(",")}: ${stdout.slice(0, 200)}`); return null; }
    const establishedDep = { key: depKey, interface: res };
    for (const loc of members) byModule.set(loc, establishedDep);
    projections.push(...res.modules);
  }
  const outPath = join(work, "interfaces.json");
  writeFileSync(outPath, canonical({ modules: projections }));
  return join("paper-interfaces", "interfaces.json");
}

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
  // interfaces where it established them, else paper-established interfaces
  // where dependencies need the paper's rules.
  const established = join("interfaces", "interfaces.json");
  const estPath = join(artifacts, established);
  const estComplete = existsSync(estPath) && (() => {
    const parsed = parseCanonical(readFileSync(estPath, "utf8"));
    return parsed !== null && !hasUnestablished(parsed);
  })();
  const interfaces = estComplete ? established : (resolvePaperInterfaces(artifacts, project) ?? established);
  if (process.env.PAPER_TRACE) process.stderr.write(`paper-rules: artifacts=${artifacts} estComplete=${estComplete} interfaces=${interfaces}\n`);
  const out = execFileSync(prototype, [sidePath, "fragment.json", interfaces,
    sourceKey(artifacts), "12"], { cwd: artifacts, encoding: "utf8", maxBuffer: 64 * 1024 * 1024, stdio: ["ignore", "pipe", process.env.PAPER_TRACE ? "inherit" : "ignore"], timeout: 300_000 });
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
      : `refused: ${process.env.PAPER_TRACE ? (parsed.refusal ?? "") : (parsed.refusal ?? "").split("\n")[0]?.slice(0, 160)}`;
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
