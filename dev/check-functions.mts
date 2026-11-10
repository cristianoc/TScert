// Checks the named functions of one file of a pretext checkout, each unit on
// its own, its neighbours read at their declared signatures:
//   node dev/check-functions.mts <pretext checkout> <file under src/> <fn1,fn2,…|*>
// `*` selects every unit of the file. The project is the checkout's own
// `tsconfig.json` with `types: []`, its tests left out. Prints one line per
// selected unit (status, members, first refusal line) and the seconds taken;
// exits 0 when every selected unit verifies.
//
// Under a refused unit's line follow every refusal its check emitted: each
// line of the refusal, its source places as `line:column` with the text
// there, the obligation's summary in source names (`diagnostic-view.mts`),
// and the facts the obligation's point requires, over its bindings' names;
// each fact the producer supplied at a statement entry that the search left
// out, with the edge into the entry that does not establish it.
// Then, where the unit's proposal drops facts: each statement or expression
// past which the producer proposes fewer facts, what dropped them (the change
// it was given, or the form the fact analysis gives none), and the facts.
// A unit's check emits one refusal: the evidence search of a graph stops at
// the first round's failure, and within a round the nodes reached only
// through a failed node are not produced, so an obligation after the first
// is unchecked rather than refused.
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { checkApart, memberName } from "../pipeline/verify-source.mts";
import { readDiagnostic, type SourceMapEntry } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
import { indexFact as fact } from "./fact-text.mts";

const [checkout, file, names, option] = process.argv.slice(2);
const explainAll = option === "--explain";
if (checkout === undefined || file === undefined || names === undefined) {
  process.stderr.write("usage: node dev/check-functions.mts <pretext checkout> <file under src/> <fn1,fn2,…|*>\n");
  process.exit(2);
}
const root = resolve(checkout);
const project = mkdtempSync(join(tmpdir(), "check-functions-"));
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({
  extends: join(root, "tsconfig.json"),
  compilerOptions: { types: [] },
  include: [join(root, "src/**/*.ts")],
  exclude: [join(root, "src/layout.test.ts")],
}, null, 2));
const all = names === "*";
const selected = all ? [] : names.split(",").filter((n) => n !== "");
const started = performance.now();
const sourcePath = join(root, "src", file);
const result = await checkApart(sourcePath, project, false, undefined, false,
  { omitted: [], select: all ? null : selected, losses: true });
const source = readFileSync(sourcePath, "utf8");

/** A source offset as `line:column`, both from 1. */
function place(offset: number): string {
  const before = source.slice(0, offset).split("\n");
  return `${before.length}:${(before.at(-1)?.length ?? 0) + 1}`;
}
/** A span's places and the start of its text, on one line. */
function located(start: number, end: number): string {
  const text = source.slice(start, end).replace(/\s+/g, " ").trim();
  return `${file}:${place(start)}-${place(end)} «${text.length > 120 ? text.slice(0, 120) + "…" : text}»`;
}
/** The binding names of a point's context, slot by slot. */
function bindings(map: SourceMapEntry | null): string[] {
  return (map?.context ?? []).map((d) =>
    d.name || (d.span === null ? "" : source.slice(d.span[0], d.span[1]).replace(/\s+/g, " ").trim()));
}
/** Every line a refused unit's check emitted, each source place located. */
function refusal(detail: string): string[] {
  const out: string[] = [];
  for (const line of detail.split("\n")) {
    if (line === "" || line.startsWith("obligation-diagnostic: ")) continue;
    out.push(line.slice(0, 400));
    for (const m of line.matchAll(/\[(\d+),(\d+)\)/g)) out.push(`  at ${located(Number(m[1]), Number(m[2]))}`);
  }
  const record = readDiagnostic(detail);
  if (record === undefined) return out;
  const summary = presentObligation(record, source).summary;
  if (summary) out.push(`  obligation: ${summary.length > 600 ? summary.slice(0, 600) + "…" : summary}`);
  for (const d of record.candidatesLeftOut ?? []) {
    const names = bindings(d.sourceMap);
    const name = (slot: number): string => names[slot] || `slot ${slot}`;
    const at = d.sourceMap === null ? `node ${d.label}` : located(...d.sourceMap.pos);
    const from = d.edgeFrom === d.label ? "the entry's assumptions" :
      d.edgeSourceMap === null ? `node ${d.edgeFrom}` : located(...d.edgeSourceMap.pos);
    const { fact: f, cond, negated } = d.fact;
    out.push(`  left out at ${at}: ${cond === undefined ? "" : `${negated ? "!" : ""}${name(cond)} → `}${fact(f, name)}`);
    out.push(`    not established by the edge from ${from}`);
  }
  const point = record.kind === "edge-coverage" ? record.destination : record.kind === "node-typing" ? record.source : null;
  if (point === null) return out;
  if (record.kind === "edge-coverage" && record.source.sourceMap !== null)
    out.push(`  edge from ${located(...record.source.sourceMap.pos)}`);
  const names = bindings(point.sourceMap);
  const name = (slot: number): string => names[slot] || `slot ${slot}`;
  for (const { fact: f, cond, negated } of point.requiredKnowledge?.indices ?? [])
    out.push(`  required: ${cond === undefined ? "" : `${negated ? "!" : ""}${name(cond)} → `}${fact(f, name)}`);
  return out;
}

const units = (result.units ?? []).filter((u) => all || u.members.some((m) => selected.includes(memberName(m))));
const seen = new Set(units.flatMap((u) => u.members.map(memberName)));
let ok: boolean = result.units !== null && result.units !== undefined && units.length > 0;
for (const u of units) {
  if (u.status !== "verified") ok = false;
  const first = u.detail.split("\n").find((l) => l !== "" && !l.startsWith("obligation-diagnostic: ")) ?? "";
  console.log(`${u.status}\t${u.members.map(memberName).join(",")}\t${first.slice(0, 400)}`);
  if (u.status !== "verified") for (const line of refusal(u.detail)) console.log(`\t${line}`);
  if (u.status !== "verified" || explainAll) for (const loss of [...(u.losses ?? [])].sort((a, b) => a.pos[0] - b.pos[0])) {
    if (loss.kind === "footprint") {
      console.log(`\tfootprint at ${located(loss.pos[0], loss.pos[1])}: ${loss.reason}`);
      continue;
    }
    console.log(`\tfacts dropped at ${located(loss.pos[0], loss.pos[1])}: ${loss.reason}`);
    for (const f of loss.facts) console.log(`\t  ${f}`);
  }
}
for (const n of selected) if (!seen.has(n)) { ok = false; console.log(`missing\t${n}\tno unit with this member`); }
if (result.units === null || result.units === undefined)
  console.log(`file-refused\t${result.status} ${result.phase ?? ""}\t${("detail" in result ? result.detail : "").split("\n")[0]?.slice(0, 400)}`);
// Unless TSCERT_EVIDENCE_REUSE=0, how many units were checked over evidence
// an earlier verifier found (docs/STAGE-STORE.md, "Evidence proposals").
if (result.reused !== undefined) console.log(`reused\t${result.reused} of ${(result.units ?? []).length} units`);
console.log(`seconds\t${((performance.now() - started) / 1000).toFixed(1)}`);
process.exit(ok ? 0 : 1);
