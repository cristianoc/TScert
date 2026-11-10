// The single pass's state at one node of a unit, over source names
// (docs/drafts/single-pass.md, "Observing"):
//   node dev/single-pass-state.mts <run dir> <source.ts> <function> <node:L | line:column | refusal>
// The run directory is a kept pipeline run of the source (its fragment.json,
// claims.json and invocations.jsonl). The pass is run again up to the node
// (`TSCERT_OBSERVE`); printed: the node's place, its bindings with their
// types, the state on entry by kind of fact, what the node's step added and
// removed, and at a merge each predecessor's facts the merge did not keep,
// with the predecessors that lack each. With `refusal`, the unit's refusal:
// its obligation, the facts over the names it mentions and those connected,
// and each fact it lacks or an earlier state held, with where that fact was
// last present and which step, edge or merge removed it.
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { isJsonList, isJsonObject, type JsonRead, type JsonValue } from "../tools/calculus.mts";
import surface from "../tools/claim-text.mts";
import { knowledgeFacts } from "./fact-text.mts";

const root = resolve(import.meta.dirname, "..");
const verifier = join(root, "lean/.lake/build/bin/verifier");
const [run, sourcePath, fn, target] = process.argv.slice(2);
if (run === undefined || sourcePath === undefined || fn === undefined || target === undefined) {
  process.stderr.write("usage: node dev/single-pass-state.mts <run dir> <source.ts> <function> <node:L | line:column>\n");
  process.exit(2);
}
const source = readFileSync(sourcePath, "utf8");
const field = (v: JsonRead, k: string): JsonRead => (isJsonObject(v) ? v[k] : undefined);
const list = (v: JsonRead): readonly JsonValue[] => (isJsonList(v) ? v : []);

/** A `line:column` place as a source offset, both from 1. */
function offset(line: number, column: number): number {
  const lines = source.split("\n");
  return lines.slice(0, line - 1).reduce((n, l) => n + l.length + 1, 0) + column - 1;
}
/** A source offset as `line:column`. */
function place(at: number): string {
  const before = source.slice(0, at).split("\n");
  return `${before.length}:${(before.at(-1)?.length ?? 0) + 1}`;
}
const spanText = (span: JsonRead): string => {
  const [a, b] = list(span);
  if (typeof a !== "number" || typeof b !== "number") return "";
  return source.slice(a, b).replace(/\s+/g, " ").trim();
};
/** A node's place and the start of its text. */
function located(map: JsonRead, label: JsonRead): string {
  const pos = list(field(map, "pos"));
  const [a, b] = pos;
  if (typeof a !== "number" || typeof b !== "number") return `node ${String(label)}`;
  const text = spanText(pos);
  return `node ${String(label)} at ${place(a)}-${place(b)} «${text.length > 100 ? text.slice(0, 100) + "…" : text}»`;
}

const log = readFileSync(join(run, "invocations.jsonl"), "utf8");
const key = /"--check-units","fragment\.json","claims\.json","([^"]+)"/.exec(log)?.[1];
if (key === undefined) throw Error("no file key in the run's invocations");
const lineColumn = /^(\d+):(\d+)$/.exec(target);
const where = lineColumn ? `offset:${offset(Number(lineColumn[1]), Number(lineColumn[2]))}` : target;
const pass = spawnSync(verifier, ["--verify-units", "3", join(run, "fragment.json"), join(run, "claims.json"), key, "12", fn],
  { encoding: "utf8", maxBuffer: 1 << 28, env: { ...process.env, TSCERT_OBSERVE: where } });
const marker = target === "refusal" ? "; refusal-observation: " : "; observation: ";
const line = pass.stderr.split("\n").find((l) => l.includes(marker));
if (line === undefined) {
  process.stdout.write(pass.stderr.split("\n").filter((l) => !l.startsWith("stamp") && !l.startsWith("rule time")).join("\n") + "\n");
  process.exit(1);
}
const record: JsonValue = JSON.parse(line.slice(line.indexOf(marker) + marker.length));

const observed = field(record, "observed");
const map = field(observed, "sourceMap");
const context = list(field(map, "context"));
const names = context.map((d, i) => {
  const n = field(d, "name");
  return typeof n === "string" && n !== "" ? n : spanText(field(d, "span")) || `slot ${i}`;
});
const name = (slot: number): string => names[slot] ?? `slot ${slot}`;
const result = spanText(field(map, "pos")) || "result";
const nameAfter = (slot: number): string => (slot === 0 ? `⟨${result.length > 40 ? result.slice(0, 40) + "…" : result}⟩` : name(slot - 1));
const types = field(record, "types") ?? null;
const typeNames = list(field(record, "names")).flatMap((p): [number, string][] =>
  isJsonList(p) && typeof p[0] === "number" && typeof p[1] === "string" ? [[p[0], p[1]]] : []);
const typeText = (labels: JsonRead): string =>
  isJsonList(labels) ? surface.printType(surface.lift(types, labels, 3, typeNames)).text : "?";
const claim = field(record, "claim");

const out: string[] = [];
out.push(located(map, field(observed, "label")));
out.push("bindings:");
list(field(claim, "context")).forEach((t, i) => out.push(`  ${name(i)} : ${typeText(t)}`));
out.push(`  result ${nameAfter(0)} : ${typeText(field(claim, "type"))}`);

// A refusal: the obligation, the facts over the names it mentions and
// those connected, each fact it lacks and each such fact an earlier state
// held, with where it was last present and what removed it.
if (target === "refusal") {
  out.push(`refused: ${String(field(record, "refusal"))}`);
  const edge = field(record, "edge");
  if (isJsonObject(edge)) out.push(`on the edge to ${located(field(edge, "sourceMap"), field(edge, "label"))}`);
  const facts = knowledgeFacts(field(record, "facts"), nameAfter);
  out.push(`facts over the obligation's names and those connected: ${facts.length}`);
  for (const f of facts) out.push(`  ${f.kind}: ${f.text}`);
  const where = (ws: JsonRead): string[] => list(ws).map((w) =>
    `    ${located(field(w, "sourceMap"), field(w, "label")).split(" «")[0]}: ${String(field(w, "why"))}`);
  const missing = list(field(record, "missing"));
  if (missing.length > 0) out.push("lacks:");
  for (const m of missing) {
    for (const f of knowledgeFacts(field(m, "fact"), nameAfter)) out.push(`  ${f.kind}: ${f.text}`);
    out.push(...where(field(m, "where")));
  }
  const lost = list(field(record, "lost"));
  out.push(`facts over these names an earlier state held: ${lost.length}`);
  for (const m of lost) {
    for (const f of knowledgeFacts(field(m, "fact"), nameAfter)) out.push(`  ${f.kind}: ${f.text}`);
    out.push(...where(field(m, "where")));
  }
  process.stdout.write(out.join("\n") + "\n");
  process.exit(0);
}
const before = knowledgeFacts(field(record, "before"), name);
const preds = list(field(record, "preds"));
out.push(`state on entry${preds.length > 0 ? " (the merge's result)" : ""}: ${before.length} facts`);
const kinds = [...new Set(before.map((f) => f.kind))];
for (const k of kinds) for (const f of before.filter((x) => x.kind === k)) out.push(`  ${k}: ${f.text}`);
for (const x of list(field(record, "implies")))
  out.push(`  implication: ${name(Number(field(x, "test")))} === true → ${name(Number(field(x, "target")))} : ${typeText(field(x, "type"))}`);
// A step refused: its state on entry alone.
if (JSON.stringify(field(record, "before")) === JSON.stringify(field(record, "after"))) {
  out.push("its step is refused");
  process.stdout.write(out.join("\n") + "\n");
  process.exit(0);
}
// The step: the facts after it over the same names (the result named
// by its text), against those on entry.
const after = knowledgeFacts(field(record, "after"), nameAfter);
const had = new Set(before.map((f) => f.text)), has = new Set(after.map((f) => f.text));
out.push("the step added:");
for (const f of after) if (!had.has(f.text)) out.push(`  ${f.kind}: ${f.text}`);
out.push("the step removed:");
for (const f of before) if (!has.has(f.text)) out.push(`  ${f.kind}: ${f.text}`);
// A merge: each predecessor's facts the result does not hold, with the
// predecessors lacking each, and for a bound the others' bounds of its form.
const predFacts = preds.map((p) => ({ at: located(field(p, "sourceMap"), field(p, "label")), facts: knowledgeFacts(field(p, "knowledge"), name) }));
const lhs = (t: string): string | null => /^(.*) (<=|!==) -?\d+$/.exec(t)?.[1] ?? null;
for (const p of predFacts) {
  out.push(`predecessor ${p.at}: ${p.facts.length} facts; not kept:`);
  for (const f of p.facts) {
    if (had.has(f.text)) continue;
    const lacking = predFacts.filter((q) => !q.facts.some((g) => g.text === f.text));
    const form = lhs(f.text);
    const others = form === null ? [] : lacking.map((q) => q.facts.find((g) => lhs(g.text) === form)?.text ?? null);
    const why = lacking.length === 0 ? "every predecessor states it"
      : `missing on ${lacking.map((q) => q.at.split(" «")[0]).join(", ")}` +
        (others.some((o) => o !== null) ? ` (there: ${others.map((o) => o ?? "none").join("; ")})` : "");
    out.push(`  ${f.kind}: ${f.text} — ${why}`);
  }
}
process.stdout.write(out.join("\n") + "\n");
