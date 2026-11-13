// The single forward pass (`verifier --verify-units 3`, docs/drafts/single-pass.md)
// against the pipeline on the pipeline cases: each case whose file name
// contains a pattern (every case with none) checked through the pipeline,
// its run kept, then the pass run over the same fragment and claims; each
// unit's two verdicts compared.
//   node dev/single-pass-agreement.mts [pattern…]
// With TSCERT_GIVEN_DIR set, each case's given statement-entry facts are read
// from <dir>/<case file>.jsonl (written by dev/single-pass-given.mts).
// With TSCERT_PASS_MODE=8, the pass runs over the fragment alone
// (`--verify-units 8`), its types computed by the verifier; with
// TSCERT_STANDINS_ALL set too, every function's and qualified import's
// footprint the case's claims state is supplied as a written-footprint
// stand-in (dev/single-pass-standins.mts).
// With TSCERT_REFEREE set (mode 8), each file is also run in mode 9, the
// search and the proved check over the same plans: a unit mode 8 accepts and
// mode 9 refuses is a hole in the pass until shown otherwise, printed as
// `hole:`; the other direction is counted. TSCERT_FORCE (passed through)
// forces an adversarial proposal (`literals`, `callees`, `elements`,
// `objects`, `spreads`, `stale`, `throws`, `guards`, `reads`, `paths`,
// `offers`, `loops`, `decided`, `schemes`, `callbacks`, `fresh`, `defaults`, `finally`, `never`, `meets`, `implications`, `binds`, `arms`, `captures`, `cells`, `early`, `no-return`, `steps`, `head-entry`, `start-facts`, `head-counters`, `head-carried`, `head-inputs`, `head-separations`, `head-paired`, `head-kinds`, `head-arms`, `head-ensures`, `head-entails`, `head-every`, `head-implications`, `head-exits`, `head-restated`, `head-guards`, `head-elements`, `head-region-values`, `head-region-cells`, `head-region-facts`, `head-region-fields`, `head-apart`, `head-called`, `head-eliminated`); the controls
// (tests/single-pass-control-inputs.mts, the suite of the single pass's controls' list) run with theirs forced whatever
// the patterns, each expected refused by mode 8; the forced proposal decides
// the control's unit and the units it depends on, the file's other units
// compared unforced.
// Prints the disagreements, then the counts: units agreeing, disagreeing,
// those the pass does not handle by construct, and those whose pipeline
// check did not finish (a stage's timeout), which decide nothing. Exits 0
// exactly when no unit disagrees, none is not handled and every case ran;
// a unit whose pipeline check did not finish is counted apart.
import { spawnSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";
import { pooled } from "../pipeline/run-cases.mts";
import { checkApart } from "../pipeline/verify-source.mts";
import { withoutEvidenceReuse } from "../pipeline/stages.mts";
import { verifyWithInterfaces } from "../pipeline/module-interfaces.mts";
import { standIns } from "./single-pass-standins.mts";
import { forcedProposals, type ForcedProposal } from "../tests/single-pass-control-inputs.mts";

const root = resolve(import.meta.dirname, "..");
// Its artifacts come from the pipeline's route (claims, the referee).
process.env.TSCERT_ROUTE ??= "pipeline";
const verifier = join(root, "lean/.lake/build/bin/verifier");
withoutEvidenceReuse();

type Verdict = { accepted: boolean; refusal: string; closed?: boolean };
type Comparison = { file: string; unit: string; pipeline: string; pass: string; agree: boolean; notHandled: string | null; why: string;
  referee: string | null; control: boolean; closed: boolean; passClosed: boolean };
/** Units the pass and the referee both accept, with every unit they depend
 * on, where the pipeline refuses: each reviewed as a safe function the
 * producer's proposal lost. They count as agreeing while both accept and the
 * pipeline refuses; any other such unit is a disagreement. */
const reviewed: { file: string; unit: string; why: string }[] = [
  { file: "blocker-pretext-equality-conjunction", unit: "runs@923", why: "the producer loses an equality's narrowing on the right operand of `&&`" },
  { file: "blocker-last-guard-param-inferred", unit: "fields@712", why: "the producer selects the plain `filter` row at an inferred union parameter" },
  { file: "blocker-gap-round-cache-answer-inferred", unit: "real@605", why: "the producer builds the callback's records at separate invariant fields" },
  { file: "invalid-bounds-callback-footprint", unit: "visit@88", why: "the callback keeps every store, so the read stays in bounds; the unit `broken` stays refused" },
  { file: "invalid-native-promise-invariant-result", unit: "widen@89", why: "the call is made at `make<unknown>`, whose result is the stated one; the producer chose `make<number>`" },
];
/** Forced proposals, the suite of the single pass's controls' list. */
const controls: readonly ForcedProposal[] = forcedProposals;
/** Forged documents: mode 3 (the pass over a claims document) accepts the
 * unit at the producer's claims and refuses it at the forged ones, with the
 * refusal stated. */
const forgedDocuments: { file: string; unit: string; forge: (claims: Record<string, unknown>, source: string) => void;
    refusal: RegExp }[] = [
  // `x` claimed `string` at the return after a saved test whose `if` has an
  // empty arm, so that both exits enter the return's node: the false exit
  // carries no narrowing (under Node `kept(1)` returns 1).
  { file: "saved-test-empty-arm", unit: "kept@453", refusal: /edge from node \d+ to node \d+/, forge: (claims, source) => {
    const types = claims.types;
    const functions = claims.functions;
    if (!Array.isArray(types) || !Array.isArray(functions)) throw new Error("claims without types or functions");
    const str = types.findIndex((t) => JSON.stringify(t) === '["str"]');
    const at = source.indexOf("return x");
    const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null;
    const fn: unknown = functions.find((f) => isRecord(f) && f.name === "kept");
    if (str < 0 || at < 0 || !isRecord(fn) || !Array.isArray(fn.entries) || !Array.isArray(fn.expressions))
      throw new Error("kept's claims");
    let forged = 0;
    for (const e of fn.entries) if (isRecord(e) && e.start === at && Array.isArray(e.bindings))
      for (const b of e.bindings) if (isRecord(b) && b.name === "x") { b.type = [str]; forged++; }
    for (const e of fn.expressions) if (isRecord(e) && Array.isArray(e.pos) && e.pos[0] === at + 7) { e.type = [str]; forged++; }
    if (forged !== 2) throw new Error(`kept's return: ${forged} claims forged`);
  } },
];

/** The file key the pipeline's check of a run named: `--check-units`'s third argument. */
function fileKey(artifacts: string): string | null {
  const log = readFileSync(join(artifacts, "invocations.jsonl"), "utf8");
  const match = /"--check-units","fragment\.json","claims\.json","([^"]+)"/.exec(log);
  return match ? match[1] : null;
}

/** The pass's verdict on each unit of a run's file. */
function passVerdicts(artifacts: string, key: string, given: string | null, mode: string = process.env.TSCERT_PASS_MODE ?? "3",
    force?: string, allCuts: boolean = false, claimsDocument: string = join(artifacts, "claims.json")): Map<string, Verdict> {
  let env: NodeJS.ProcessEnv = given === null ? process.env : { ...process.env, TSCERT_GIVEN: given };
  if (force !== undefined) env = { ...env, TSCERT_FORCE: force };
  if (allCuts) env = { ...env, TSCERT_ALL_CUTS: "1" };
  if ((mode === "8" || mode === "9") && process.env.TSCERT_STANDINS_ALL !== undefined) {
    const path = join(artifacts, "standins.json");
    writeFileSync(path, standIns(join(artifacts, "claims.json")) + "\n");
    env = { ...env, TSCERT_STANDINS: path };
  }
  // Modes 8 and 9 read the fragment alone.
  const documents = mode === "8" || mode === "9" ? [join(artifacts, "fragment.json")]
    : [join(artifacts, "fragment.json"), claimsDocument];
  let run: { stdout: string; stderr: string };
  if (mode === "8" || mode === "9") {
    const emptyGiven = join(artifacts, "empty-given.jsonl");
    const emptyStandins = join(artifacts, "empty-standins.json");
    writeFileSync(emptyGiven, "");
    writeFileSync(emptyStandins, '{"functions":[],"imports":[]}');
    run = verifyWithInterfaces(documents[0], key, "", {
      mode: mode === "8" ? 8 : 9, fuel: 12, rounds: 4096, force: force?.split(",") ?? [], allCuts,
      standins: env.TSCERT_STANDINS ?? emptyStandins,
      given: given !== null && existsSync(given) ? given : emptyGiven, work: join(artifacts, "interfaces"),
      invocation: { limitMs: 60_000, force: false, recorder: null },
    }).run;
  } else run = spawnSync(verifier, ["--verify-units", mode, ...documents, key, "12"],
    { encoding: "utf8", maxBuffer: 1 << 28, env });
  const verdicts = new Map<string, Verdict>();
  const dependencies = new Map<string, string[]>();
  for (const line of run.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const value: unknown = JSON.parse(line);
    if (typeof value !== "object" || value === null) continue;
    const unit = "unit" in value ? value.unit : undefined;
    if (typeof unit !== "string") continue;
    const refusal = "refusal" in value && typeof value.refusal === "string" ? value.refusal : "";
    verdicts.set(unit, { accepted: "accepted" in value && value.accepted === true, refusal });
    const depends = "depends" in value && Array.isArray(value.depends) ? value.depends.filter((d) => typeof d === "string") : [];
    dependencies.set(unit, depends);
  }
  // `closed`: the unit's acceptance with every unit of the file it depends
  // on accepted; a refused dependency refuses it. The per-unit verdict stays
  // what the pipeline's is compared with.
  for (const v of verdicts.values()) v.closed = v.accepted;
  for (let changed = true; changed; ) {
    changed = false;
    for (const [unit, v] of verdicts) {
      // A module unit it depends on (`module:<location>#<unit>`) counts only
      // where its own line is printed.
      if (v.closed === true && (dependencies.get(unit) ?? []).some((d) => verdicts.get(d)?.closed === false ||
          (d.startsWith("module:") && !verdicts.has(d)))) {
        v.closed = false;
        changed = true;
      }
    }
  }
  return verdicts;
}

/** The construct a refusal says the pass does not handle. */
function construct(refusal: string): string | null {
  const match = /not handled: ([^:(]*?)(?: at node \d+)?(?:[:(]|$)/.exec(refusal);
  return match ? match[1].trim() : null;
}

async function compare(test: Case): Promise<Comparison[]> {
  const source = join(root, "pipeline/examples", `${test.file}.ts`);
  using outcome = await checkApart(source, test.project ? resolve(root, test.project) : undefined,
    test.typescriptErrors, undefined, true);
  // A certified import's module run is checked apart (`--check-module`).
  const units = (outcome.units ?? []).filter((u) => !u.unit.startsWith("module:"));
  // A file whose pipeline check did not finish (a stage's timeout) gives no
  // units: counted as one unfinished entry rather than dropped.
  if (units.length === 0 && outcome.status === "error")
    return [{ file: test.file, unit: "(file)", pipeline: "unfinished", pass: "missing", agree: false, notHandled: null, why: "", referee: null, control: false, closed: false, passClosed: false }];
  // A file the pipeline decides with no unit checked (its producer or its
  // claims refused) is run from its fragment all the same in mode 8: each
  // unit the pass gives is compared with the file's outcome.
  const fragment = join(outcome.artifacts, "fragment.json");
  const fragmentValue = (): unknown => existsSync(fragment) ? JSON.parse(readFileSync(fragment, "utf8")) : null;
  const fragmentFile = (): string | null => {
    const value = fragmentValue();
    return typeof value === "object" && value !== null && "file" in value && typeof value.file === "string" ? value.file : null;
  };
  // The unit a whole-file refusal is located in: the function whose extent
  // (its name to the last span its body names) holds the refusal's first
  // position, else the initialization.
  const locatedUnit = (): string | null => {
    const detail = outcome.status === "verified" ? "" : outcome.detail;
    const at = /\[(\d+),\d+\)/.exec(detail);
    if (at === null) return null;
    const p = Number(at[1]);
    const value = fragmentValue();
    const functions = typeof value === "object" && value !== null && "functions" in value && Array.isArray(value.functions) ? value.functions : [];
    const ends = (v: unknown): number => {
      if (Array.isArray(v)) return Math.max(0, ...v.map(ends));
      if (typeof v !== "object" || v === null) return 0;
      let m = 0;
      for (const [k, x] of Object.entries(v)) {
        if ((k === "pos" || k === "span") && Array.isArray(x) && typeof x[1] === "number") m = Math.max(m, x[1]);
        m = Math.max(m, ends(x));
      }
      return m;
    };
    for (const f of functions) {
      if (typeof f !== "object" || f === null || !("namePos" in f) || !Array.isArray(f.namePos) || !("name" in f)) continue;
      const start = f.namePos[0];
      if (typeof start === "number" && start <= p && p < ends("body" in f ? f.body : null)) return `${String(f.name)}@${start}`;
    }
    return "init";
  };
  const whole = units.length === 0;
  if (whole && process.env.TSCERT_PASS_MODE !== "8") return [];
  const key = whole ? fragmentFile() : fileKey(outcome.artifacts);
  if (key === null) return [];
  const givenDir = process.env.TSCERT_GIVEN_DIR;
  const given = givenDir === undefined ? null : join(givenDir, `${test.file}.jsonl`);
  const control = controls.find((c) => c.file === test.file);
  const force = process.env.TSCERT_FORCE;
  // A control's forced proposal decides the control's unit, with the units
  // it depends on forced too; the file's other units are compared unforced.
  const decide = (mode: string | undefined, forced: string | undefined, allCuts = false): Map<string, Verdict> => {
    const verdicts = passVerdicts(outcome.artifacts, key, given, mode, forced, allCuts);
    if (control === undefined) return verdicts;
    if (control.positive && forced === undefined && verdicts.get(control.unit)?.closed !== true)
      throw new Error(`positive control refused unforced: ${test.file} ${control.unit}`);
    // Accepted only with every unit it depends on accepted under the force.
    const own = passVerdicts(outcome.artifacts, key, given, mode, control.force, allCuts).get(control.unit);
    if (own === undefined) verdicts.delete(control.unit);
    else verdicts.set(control.unit, own.closed === true ? own
      : { ...own, accepted: false, refusal: own.refusal === "" ? "a unit it depends on refused" : own.refusal });
    return verdicts;
  };
  const pass = decide(undefined, force);
  const forgedDocument = forgedDocuments.find((d) => d.file === test.file);
  if (forgedDocument !== undefined) {
    const honest = passVerdicts(outcome.artifacts, key, null, "3").get(forgedDocument.unit);
    if (honest?.accepted !== true)
      throw new Error(`forged-document control refused at the producer's claims: ${test.file} ${forgedDocument.unit}`);
    const claims: unknown = JSON.parse(readFileSync(join(outcome.artifacts, "claims.json"), "utf8"));
    if (typeof claims !== "object" || claims === null || Array.isArray(claims)) throw new Error("claims not an object");
    const record = Object.fromEntries(Object.entries(claims));
    forgedDocument.forge(record, readFileSync(source, "utf8"));
    const document = join(outcome.artifacts, "forged-claims.json");
    writeFileSync(document, JSON.stringify(record));
    const forged = passVerdicts(outcome.artifacts, key, null, "3", undefined, false, document).get(forgedDocument.unit);
    if (forged === undefined || forged.accepted || !forgedDocument.refusal.test(forged.refusal))
      throw new Error(`forged-document control not refused as stated: ${test.file} ${forgedDocument.unit}: ${forged?.refusal ?? "missing"}`);
  }
  // The referee accepts a unit where the search finds evidence the proved
  // check accepts with the search's cuts at the loop heads, or else at every
  // statement entry: either is a certificate of the same proposals.
  let referee = process.env.TSCERT_REFEREE === undefined ? null : decide("9", force);
  if (referee !== null && [...pass].some(([u, v]) => v.accepted && referee?.get(u)?.accepted !== true)) {
    const again = decide("9", force, true);
    for (const [u, v] of again) if (v.accepted) referee.set(u, v);
  }
  // Of a file the pipeline refuses whole, the unit its refusal is located
  // in is refused; the others, and every unit where the refusal names no
  // position, are undecided.
  const located = whole && outcome.status !== "verified" ? locatedUnit() : null;
  const compared: { unit: string; status: string }[] = whole
    ? [...pass.keys()].filter((u) => !u.startsWith("module:")).map((unit) => ({ unit,
        status: outcome.status === "verified" ? "verified" : located === unit ? "refused" : "undecided" }))
    : units;
  return compared.map((u): Comparison => {
    const v = pass.get(u.unit);
    const notHandled = v ? construct(v.refusal) : null;
    const passSays = v === undefined ? "missing" : v.accepted ? "verified" : notHandled ? "not handled" : "refused";
    // A pipeline run that did not finish (a stage's timeout) decides nothing.
    const pipelineSays = u.status === "verified" ? "verified" : u.status === "error" ? "unfinished"
      : u.status === "undecided" ? "undecided" : "refused";
    const r = referee?.get(u.unit);
    const refereeSays = referee === null ? null : r === undefined ? "missing" : r.accepted ? "verified" : "refused";
    // Both accept with their dependencies accepted.
    const closed = v?.closed === true && (referee === null || r?.closed === true);
    return { file: test.file, unit: u.unit, pipeline: pipelineSays, pass: passSays,
      agree: control?.positive && control.unit === u.unit ? passSays === "refused" : passSays === pipelineSays ||
        (pipelineSays === "refused" && passSays === "verified" && refereeSays === "verified" && closed &&
          reviewed.some((k) => k.file === test.file && k.unit === u.unit)), notHandled, why: v ? v.refusal.replace(/\s+/g, " ").slice(0, 160) : "",
      referee: refereeSays, control: control?.unit === u.unit, closed, passClosed: v?.closed === true };
  });
}

const patterns = process.argv.slice(2);
const chosen = cases.filter((c) => patterns.length === 0 || patterns.some((p) => c.file.includes(p)) ||
  (process.env.TSCERT_PASS_MODE === "8" && controls.some((k) => k.file === c.file)));
const results = await pooled(chosen, compare);
const compared: Comparison[] = [];
for (const [i, r] of results.entries()) {
  if (r.status === "fulfilled") compared.push(...r.value);
  else process.stdout.write(`${chosen[i].file}: ${String(r.reason).slice(0, 200)}\n`);
}
// The units of a file the pipeline refuses whole, but the one its refusal
// is located in, are undecided: counted apart.
const all = compared.filter((c) => c.pipeline !== "undecided");
const undecided = compared.filter((c) => c.pipeline === "undecided");
if (undecided.length > 0)
  process.stdout.write(`${undecided.length} units of files the pipeline refuses before any unit's check, ` +
    `outside the refusal's unit: the pass accepts ${undecided.filter((c) => c.pass === "verified").length}\n`);
for (const c of undecided.filter((c) => c.pass === "verified"))
  process.stdout.write(`undecided, the pass accepts: ${c.file} ${c.unit}\n`);
const constructs = new Map<string, number>();
for (const c of all) {
  const what = c.notHandled?.replace(/ at node \d+$/, "") ?? null;
  if (what !== null) constructs.set(what, (constructs.get(what) ?? 0) + 1);
  else if (!c.agree && c.pipeline !== "unfinished") process.stdout.write(`disagree: ${c.file} ${c.unit}: pipeline ${c.pipeline}, pass ${c.pass}: ${c.why}\n`);
}
const unfinished = all.filter((c) => c.pipeline === "unfinished").length;
const agree = all.filter((c) => c.agree).length;
const handled = all.filter((c) => c.notHandled === null && c.pipeline !== "unfinished");
process.stdout.write(`${all.length} units of ${chosen.length} cases: ${agree} agree, ` +
  `${handled.length - handled.filter((c) => c.agree).length} disagree, ${all.filter((c) => c.notHandled !== null).length} not handled, ` +
  `${unfinished} the pipeline did not finish\n`);
for (const [what, n] of [...constructs].sort((a, b) => b[1] - a[1])) process.stdout.write(`  not handled: ${what} ${n}\n`);
// The referee: units mode 8 accepts and mode 9 refuses (holes), and the
// other direction (the pass's incompleteness), counted.
const refereed = all.filter((c) => c.referee !== null);
const holes = refereed.filter((c) => c.pass === "verified" && c.referee !== "verified");
for (const c of holes) process.stdout.write(`hole: ${c.file} ${c.unit}: mode 8 accepts, mode 9 ${c.referee}, pipeline ${c.pipeline}\n`);
const refereeOnly = refereed.filter((c) => c.pass !== "verified" && c.referee === "verified");
for (const c of refereeOnly) process.stdout.write(`referee only: ${c.file} ${c.unit}: mode 9 accepts, mode 8 ${c.pass}, pipeline ${c.pipeline}\n`);
const bothAccept = refereed.filter((c) => c.closed && c.pipeline === "refused");
for (const c of bothAccept)
  process.stdout.write(`both accept, pipeline refuses${c.agree ? " (reviewed)" : ""}: ${c.file} ${c.unit}\n`);
if (refereed.length > 0)
  process.stdout.write(`referee: ${holes.length} mode 8 accepts / mode 9 refuses, ` +
    `${refereeOnly.length} mode 9 accepts / mode 8 refuses\n`);
// The controls: each refused by mode 8 under its forced proposal, a unit's
// acceptance counting only with every unit it depends on accepted.
const controlFailures = all.filter((c) => c.control && c.passClosed);
for (const c of controlFailures) process.stdout.write(`control accepted: ${c.file} ${c.unit}\n`);
// The correctness half of the performance gate: every unit whose pipeline
// check finished agrees, none is not handled, and every case ran.
const failedCases = results.filter((r) => r.status === "rejected").length;
const disagreeing = handled.length - handled.filter((c) => c.agree).length;
const notHandled = all.filter((c) => c.notHandled !== null).length;
process.exitCode = disagreeing === 0 && notHandled === 0 && failedCases === 0 && holes.length === 0 &&
  controlFailures.length === 0 ? 0 : 1;
