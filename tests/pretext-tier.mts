// The pretext tier (`make test-pretext`): what an agent adding a bounds
// capability for pretext runs, in place of the whole suite and the census.
//   node tests/pretext-tier.mts --pretext <checkout> [--files a.ts,b.ts] [--update]
// Three parts, each against its recorded expectation:
// 1. the bounds pattern cases (`bounds-pattern-*` of pipeline/cases.mts): a
//    gap now verified is a pattern the capability closed, to be restated
//    as a positive case;
// 2. `boundsList` below, the existing cases of the mechanisms a bounds
//    capability extends;
// 3. pretext's functions, each file of the checkout's `src/` checked unit
//    by unit, against `pretext-tier-expected.json`'s record for the
//    checkout's commit: a function verified there and not here fails the
//    tier, one verified here and not there is reported as gained.
// `--update` records the selected files' functions for the checkout's commit.
// Stages replay from the stage store; the summary counts the stage
// invocations each part executed and replayed.
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { cases, type Case } from "../pipeline/cases.mts";
import { expectOutcome, pooled } from "../pipeline/run-cases.mts";
import { checkApart, invocationLog, memberName, type Outcome } from "../pipeline/verify-source.mts";
import { initOmission } from "../tools/fragment-parse.mts";
import { readInvocationLog } from "../pipeline/stages.mts";
import { linkFixtures } from "../pipeline/fixture-links.mts";

type Listed = { file: string; why: string };
/** Each listed case with the mechanism it stands for, one reason a group. */
const group = (why: string, files: string[]): Listed[] => files.map((file) => ({ file, why }));

/** The existing cases of the mechanisms a bounds capability extends: linear
 * facts and preconditions, written postconditions, quantified element
 * facts, frames and regions, type invariants and guards, typed arrays,
 * cursors, lazy caches, native length contracts, and the pretext shapes
 * the patterns document names as supported. */
export const boundsList: Listed[] = [
  ...group("pretext clauses: linear bounds, orderings, element paths, postconditions, disjunctions", [
    "pretext-clause-locals", "invalid-pretext-clause-locals", "pretext-clause-order", "invalid-pretext-clause-order",
    "pretext-clause-element-path", "invalid-pretext-clause-element-path", "pretext-clause-postcondition-import",
    "pretext-clause-postcondition", "invalid-pretext-clause-postcondition", "pretext-clause-disjunction",
    "invalid-pretext-clause-disjunction"]),
  ...group("preconditions and linear facts (ARITHMETIC.md)", [
    "precondition", "invalid-precondition-call", "precondition-lengths", "invalid-precondition-lengths",
    "invalid-precondition-lengths-shrunk", "invalid-precondition-literal-index", "invalid-precondition-body",
    "precondition-exported", "precondition-value-import", "invalid-precondition-value-import",
    "precondition-disjunction-refused", "closure-precondition", "invalid-closure-precondition-call",
    "table-constant-stride", "invalid-table-constant-stride", "literal-constant-value", "invalid-literal-constant-value",
    "field-path-reads", "invalid-field-path-read-at-length", "invalid-field-path-read-other-record",
    "invalid-field-path-read-replaced", "field-path-precondition-unestablished", "field-write-refinement",
    "loop-invariant-reads", "invalid-loop-invariant-back-edge", "invalid-loop-invariant-entry"]),
  ...group("written postconditions (P2's two-state posts extend them)", [
    "written-ensures", "written-ensures-value-import", "invalid-written-ensures-body", "invalid-written-ensures-unstated",
    "written-ensures-push-refused", "written-ensures-reassigned-refused", "written-ensures-default-refused",
    "written-ensures-old-refused", "assignment-call-postcondition", "invalid-assignment-call-postcondition",
    "invalid-false-ensures-value-import"]),
  ...group("native length contracts (P14)", [
    "native-length-literal", "invalid-native-length-literal", "native-length-map", "native-length-push",
    "invalid-native-length-map", "invalid-native-length-push", "native-length-indexof", "native-length-filled",
    "invalid-native-length-indexof", "invalid-native-length-filled"]),
  ...group("quantified element facts (P3, P6, P12, P13)", [
    "quantified-element-reads", "invalid-quantified-element-read-inclusive", "invalid-quantified-element-read-alias-write",
    "invalid-quantified-element-read-shrunk", "quantified-empty-builder", "invalid-quantified-empty",
    "quantified-push-builder", "invalid-quantified-push-value", "invalid-quantified-push-alias",
    "invalid-quantified-push-shrunk", "quantified-freshness-frame", "quantified-freshness-write",
    "quantified-freshness-builder", "invalid-quantified-freshness-field-alias", "invalid-quantified-freshness-free-term",
    "quantified-shadowed-builder", "bounds-quantified-invariant", "invalid-bounds-quantified-invariant",
    "every-elements-map-join", "every-elements-number", "every-elements-sparse", "invalid-every-elements-callback-call",
    "invalid-every-elements-guard-call", "invalid-every-elements-escape"]),
  ...group("frames, regions and freshness (P1, P4, P6; FOOTPRINTS.md)", [
    "bounds-callback-footprint", "invalid-bounds-callback-footprint", "stated-argument-path", "stated-local-runs",
    "invalid-stated-alias", "stated-distinct-view-refused", "stated-region-grow-keeps-lengths",
    "stated-region-stable-apart-writes", "stated-region-nullable-apart", "stated-region-nullable-apart-assigned",
    "stated-region-nullable-apart-undefined", "invalid-stated-region-nullable-reassigned",
    "invalid-stated-region-nullable-alias", "invalid-stated-region-nullable-wrong-guard",
    "invalid-stated-region-nullable-other-guard", "invalid-stated-region-unstable-apart-write", "stated-region-fresh",
    "stated-region-lazy", "invalid-stated-region-fresh-wrapper", "invalid-stated-region-fresh-join",
    "invalid-stated-region-fresh-call", "stated-fresh-direct", "invalid-stated-fresh-parameter", "stated-fresh-field",
    "stated-fresh-field-local", "stated-fresh-field-nullable", "stated-fresh-field-escape", "stated-fresh-field-alias",
    "stated-fresh-field-throw", "invalid-stated-fresh-old-array", "invalid-stated-fresh-join",
    "invalid-stated-fresh-reassigned", "invalid-stated-fresh-reassigned-throw", "stated-slot-collect",
    "stated-slot-conditional", "stated-slot-handler", "invalid-stated-slot-handler", "push-keeps-apart-lengths",
    "invalid-push-keeps-apart-lengths-alias", "push-keeps-fresh-lengths", "invalid-push-keeps-fresh-lengths-alias",
    "module-dictionary-keeps-lengths"]),
  ...group("stable operations under callbacks (FOOTPRINTS.md)", [
    "map-fresh-controls-sparse", "map-stable-fresh-store", "map-fresh-handler-refused", "invalid-map-handler-after-pop",
    "map-stable-regexp-replace", "map-stable-local-counter", "map-stable-element-write", "map-stable-push",
    "map-stable-helper", "map-stable-outer-cell", "map-stable-set", "invalid-method-effect-throw-caught",
    "invalid-map-unstable-pop"]),
  ...group("type invariants and guarded facts (P18, P20)", [
    "type-invariant-walker", "invalid-type-invariant-constructor", "invalid-type-invariant-push",
    "invalid-type-invariant-cast", "guarded-invariant-nullable", "invalid-guarded-invariant-short",
    "invalid-guarded-invariant-other-field", "guarded-invariant-optional", "guarded-conditional-arm",
    "invalid-guarded-conditional-other-field", "guarded-return", "invalid-guarded-return"]),
  ...group("cursors, loop cells and lazy caches (P16, P17)", [
    "cursor-invariant-after-writing-call", "invalid-cursor-invariant-step-back", "cursor-invariant-view-path",
    "invalid-view-path-field-replaced", "cursor-invariant-loop-write", "cursor-nested-update", "bounds-cell-invariant",
    "invalid-bounds-cell-invariant", "lazy-cache-keeps-facts", "invalid-lazy-cache-initializer-pops",
    "bounds-imported-alias-path", "invalid-bounds-imported-alias-path", "bounds-captured-precondition-gap",
    "bounds-default-precondition-gap"]),
  ...group("typed arrays: lengths, element facts, prefixes (P5, P13, P21)", [
    "typed-array-views", "invalid-typed-array-write-past-end", "invalid-typed-array-subclass", "typed-array-float64",
    "invalid-typed-array-float64-subclass", "typed-array-length-across-field-write",
    "invalid-typed-array-length-across-field-write-other", "typed-array-length-builder", "invalid-typed-array-length-short",
    "invalid-typed-array-length-fraction", "typed-array-element-facts", "invalid-typed-array-element-read-inclusive",
    "typed-array-element-writes", "invalid-typed-array-element-write-int32-wrap",
    "invalid-typed-array-element-write-uint8-truncation", "invalid-typed-array-element-write-value",
    "typed-array-subarray-facts-gap", "invalid-typed-array-element-read-after-write", "typed-array-prefix-write",
    "invalid-typed-array-prefix-past", "invalid-typed-array-prefix-value", "invalid-typed-array-prefix-int32-wrap",
    "typed-array-prefix-postfix-gap", "invalid-typed-array-prefix-cursor", "typed-array-reads-below-length",
    "typed-array-length-at-sum", "invalid-typed-array-length-at-sum", "invalid-typed-array-read-at-length",
    "invalid-typed-array-read-other-length"]),
  ...group("pretext's bounds blockers, closed (census reasons of pretext's functions)", [
    "blocker-pretext-typed-array-element-assertion", "blocker-pretext-field-assertion-after-call",
    "blocker-pretext-widened-key-read", "blocker-pretext-new-array-fill", "blocker-pretext-module-cache-write",
    "blocker-pretext-local-assertion-correlated", "blocker-pretext-parallel-element-assertion",
    "blocker-pretext-parallel-element-cast", "blocker-pretext-argument-implied-assertion",
    "blocker-pretext-conditional-test-correlated", "blocker-pretext-module-cells-apart",
    "blocker-pretext-module-cell-after-call", "blocker-pretext-sibling-field-write", "blocker-pretext-loop-exit-assigned",
    "blocker-pretext-equality-conjunction", "blocker-pretext-masked-kind-cast", "blocker-pretext-loop-cell-call-result",
    "blocker-pretext-code-point-at-assertion", "blocker-pretext-constant-implication-conjunction",
    "blocker-pretext-unary-footprint", "blocker-pretext-constant-implication-statements"]),
];

/** A pretext file's functions, each `verified` or its refusal's first line;
 * the initialization is the member `:init`. */
type FileRecord = Record<string, string>;
type Expected = Record<string, Record<string, FileRecord>>;
const examples = join(import.meta.dirname, "../pipeline/examples");
const expectedPath = join(import.meta.dirname, "pretext-tier-expected.json");
/** The recorded expectations: per commit, per file, each function's record. */
function readExpected(text: string): Expected {
  const value: unknown = JSON.parse(text);
  const record = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
  if (!record(value)) throw Error(`${expectedPath}: not an object`);
  const out: Expected = {};
  for (const [commit, files] of Object.entries(value)) {
    if (!record(files)) throw Error(`${expectedPath}: ${commit} holds no files`);
    out[commit] = {};
    for (const [file, functions] of Object.entries(files)) {
      if (!record(functions)) throw Error(`${expectedPath}: ${commit} ${file} holds no functions`);
      const kept: FileRecord = {};
      for (const [name, line] of Object.entries(functions)) {
        if (typeof line !== "string") throw Error(`${expectedPath}: ${commit} ${file} ${name} is no string`);
        kept[name] = line;
      }
      out[commit][file] = kept;
    }
  }
  return out;
}
/** pretext's files the tier checks by default: `src/` without its tests and data. */
const pretextFiles = ["analysis.ts", "checked.ts", "gecko-line-breaks.ts", "graphemes.ts", "han-kerning.ts", "layout.ts",
  "line-break.ts", "line-breaks.ts", "line-text.ts", "measurement.ts", "prepare.ts", "rich-inline.ts"];

const verifiedMark = "verified";
/** A record's functions, its initialization left out, those verified and all. */
const verifiedIn = (r: FileRecord): string[] => Object.keys(r).filter((m) => m !== initOmission && r[m] === verifiedMark);
const functionsIn = (r: FileRecord): string[] => Object.keys(r).filter((m) => m !== initOmission);

/** Stage invocations of the runs a part made: those executed, by stage, and
 * those replayed or ending otherwise. */
type Counts = { executed: Map<string, number>; replayed: number; other: number };
const counts = (): Counts => ({ executed: new Map(), replayed: 0, other: 0 });
function count(result: Outcome, into: Counts): void {
  for (const r of readInvocationLog(join(result.artifacts, invocationLog))) {
    if (r.execution === "executed") into.executed.set(r.stage, (into.executed.get(r.stage) ?? 0) + 1);
    else if (r.execution === "replayed") into.replayed++;
    else into.other++;
  }
}
function stages(c: Counts): string {
  const executed = [...c.executed.values()].reduce((a, b) => a + b, 0);
  const which = [...c.executed].map(([stage, n]) => `${stage} ${n}`).join(", ");
  return `stages ${executed} executed${which ? ` (${which})` : ""}, ${c.replayed} replayed` + (c.other ? `, ${c.other} other` : "");
}
const seconds = (since: number): string => `${((performance.now() - since) / 1000).toFixed(1)} s`;

/** Run cases against their expectations; one line for each that is not as expected. */
async function runListed(selected: Case[], into: Counts): Promise<{ failures: string[]; byKind: Map<string, number> }> {
  const settled = await pooled(selected, (c) => checkCase(c, into));
  const failures: string[] = [];
  const byKind = new Map<string, number>();
  for (const [i, c] of selected.entries()) {
    const s = settled[i];
    if (s.status === "rejected") {
      failures.push(`${c.file}: ${s.reason instanceof Error ? s.reason.message.split("\n")[0] : String(s.reason)}`);
      continue;
    }
    try {
      expectOutcome(c, s.value);
      const label = c.kind === "positive" ? "verified" : c.kind === "gap" ? "gap, refused as expected" : "unsafe, refused";
      byKind.set(label, (byKind.get(label) ?? 0) + 1);
    } catch (error) {
      const closed = c.kind === "gap" && s.value.status === "verified";
      failures.push(closed ? `${c.file}: GAP CLOSED, verified (restate it as a positive case)` :
        `${c.file}: ${error instanceof Error ? error.message.split("\n")[0].slice(0, 300) : String(error)}`);
    }
  }
  return { failures, byKind };
}
/** One case's outcome, as `run-cases.mts` checks it, its stage invocations
 * counted before its run directory is removed. */
async function checkCase(c: Case, into: Counts): Promise<Outcome> {
  using result = await checkApart(join(examples, `${c.file}.ts`),
    c.project ? resolve(import.meta.dirname, "..", c.project) : undefined, c.typescriptErrors, undefined, true);
  count(result, into);
  const { [Symbol.dispose]: _, ...outcome } = result;
  return outcome;
}

/** One pretext file checked unit by unit, as `dev/check-functions.mts` checks it. */
async function checkPretextFile(root: string, project: string, file: string, into: Counts): Promise<FileRecord | string> {
  using result = await checkApart(join(root, "src", file), project, false, undefined, true, { omitted: [], select: null });
  count(result, into);
  if (result.units === null || result.units === undefined)
    return `the file is refused: ${result.status} ${result.phase}: ${"detail" in result ? result.detail.split("\n")[0] : ""}`;
  const record: [string, string][] = [];
  for (const u of result.units) {
    const line = u.status === "verified" ? verifiedMark :
      (u.detail.split("\n").find((l) => l !== "" && !l.startsWith("obligation-diagnostic: ")) ?? u.status).slice(0, 300);
    for (const m of u.members.map(memberName)) record.push([m, line]);
  }
  return Object.fromEntries(record.sort(([a], [b]) => a.localeCompare(b)));
}

const args = process.argv.slice(2);
const option = (name: string): string | undefined => {
  const at = args.indexOf(name);
  return at < 0 ? undefined : args[at + 1];
};
const checkout = option("--pretext");
if (checkout === undefined) {
  process.stderr.write("usage: node tests/pretext-tier.mts --pretext <checkout> [--files a.ts,b.ts] [--update]\n");
  process.exit(2);
}
const update = args.includes("--update");
const files = (option("--files") ?? "").split(",").filter((f) => f !== "");
const selectedFiles = files.length ? files : pretextFiles;
const started = performance.now();
linkFixtures();
let failed: boolean = false;
const out: string[] = [];

// pretext's files are queued first, their checks the longest, then the
// pattern cases and the list; all share `checkApart`'s pool of workers.
const root = resolve(checkout);
const head = spawnSync("git", ["-C", root, "rev-parse", "HEAD"], { encoding: "utf8" }).stdout.trim();
const dirty = spawnSync("git", ["-C", root, "status", "--porcelain", "--", "src"], { encoding: "utf8" }).stdout.trim() !== "";
const project = mkdtempSync(join(tmpdir(), "pretext-tier-"));
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({
  extends: join(root, "tsconfig.json"), compilerOptions: { types: [] },
  include: [join(root, "src/**/*.ts")], exclude: [join(root, "src/layout.test.ts")],
}, null, 2));
const pretextCounts = counts();
let pretextTime = "";
const pretextChecks = Promise.all(selectedFiles.map((f) => checkPretextFile(root, project, f, pretextCounts)))
  .finally(() => { pretextTime = seconds(started); });

const patternCases = cases.filter((c) => c.file.includes("bounds-pattern-"));
const listed = boundsList.map((l) => {
  const c = cases.find((x) => x.file === l.file);
  if (c === undefined) throw Error(`boundsList names ${l.file}, which is no case of pipeline/cases.mts`);
  return c;
});
const caseCounts = counts();
const [patterns, list] = await Promise.all([runListed(patternCases, caseCounts), runListed(listed, caseCounts)]);
const caseTime = seconds(started);
for (const [name, part, total] of [["pattern cases", patterns, patternCases.length], ["list cases", list, listed.length]] as const) {
  if (part.failures.length) failed = true;
  out.push(`${name}: ${total - part.failures.length} of ${total} as expected (` +
    [...part.byKind].map(([k, n]) => `${n} ${k}`).join(", ") + `)`);
  for (const f of part.failures) out.push(`  NOT AS EXPECTED ${f}`);
}
out.push(`  cases: done at ${caseTime}, ${stages(caseCounts)}`);

const records = await pretextChecks;
rmSync(project, { recursive: true, force: true });
const expected: Expected = readExpected(readFileSync(expectedPath, "utf8"));
const atHead = expected[head];
if (update) {
  const next = { ...(atHead ?? {}) };
  for (const [i, f] of selectedFiles.entries()) {
    const r = records[i];
    if (typeof r === "string") { failed = true; out.push(`pretext ${f}: ${r}; not recorded`); }
    else next[f] = r;
  }
  expected[head] = Object.fromEntries(Object.entries(next).sort(([a], [b]) => a.localeCompare(b)));
  writeFileSync(expectedPath, JSON.stringify(expected, null, 2) + "\n");
  out.push(`pretext: recorded ${selectedFiles.length} files at ${head.slice(0, 8)}${dirty ? " (src/ has uncommitted changes)" : ""}`);
}
let total: number = 0, verified: number = 0;
out.push(`pretext at ${head.slice(0, 8)}${dirty ? " with uncommitted changes in src/" : ""}:`);
for (const [i, f] of selectedFiles.entries()) {
  const r = records[i];
  const was = atHead?.[f];
  const lost: string[] = [], gained: string[] = [], changed: string[] = [];
  if (typeof r === "string") {
    failed = true;
    out.push(`  ${f}: ${r}`);
    continue;
  }
  const n = functionsIn(r).length;
  total += n;
  verified += verifiedIn(r).length;
  if (was === undefined && !update) {
    failed = true;
    out.push(`  ${f}: ${verifiedIn(r).length} of ${n} functions verified; no expectation for ${head.slice(0, 8)} (--update records one)`);
    continue;
  }
  if (was !== undefined) {
    for (const [name, line] of Object.entries(was)) {
      const now = r[name];
      if (line === verifiedMark && now !== verifiedMark) lost.push(name);
      else if (line !== verifiedMark && now === verifiedMark) gained.push(name);
      else if (now !== undefined && now !== line) changed.push(name);
    }
    for (const [name, line] of Object.entries(r)) if (!(name in was)) (line === verifiedMark ? gained : changed).push(name);
  }
  if (lost.length) failed = true;
  const wasCount = was === undefined ? "" : ` (recorded ${verifiedIn(was).length} of ${functionsIn(was).length})`;
  const init = r[initOmission] === undefined ? "" : r[initOmission] === verifiedMark ? ", initialization verified" : ", initialization refused";
  out.push(`  ${f}: ${verifiedIn(r).length} of ${n} functions verified${wasCount}${init}`);
  for (const name of lost) out.push(`    LOST ${name}: ${r[name] ?? "no unit with this function"}`);
  for (const name of gained) out.push(`    gained ${name}`);
  for (const name of changed) out.push(`    refused ${was !== undefined && name in was ? "differently" : "(new)"} ${name}: ${r[name]}`);
}
out.push(`  pretext: ${verified} of ${total} functions verified in ${selectedFiles.length} files; done at ${pretextTime}, ${stages(pretextCounts)}`);
out.push(`${failed ? "FAILED" : "passed"}; wall ${seconds(started)}`);
process.stdout.write(out.join("\n") + "\n");
process.exit(failed ? 1 : 0);
