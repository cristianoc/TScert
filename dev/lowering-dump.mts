/* Prints the execution graphs a source's functions lower to, as the verifier
 * itself reports them (`verifier --lower-control-flow`), the graphs the
 * single pass walks. One line per node: its id, its action with the source
 * it covers, and where control goes next; under it, the source each of its
 * executions evaluates. A record's author starts from this output when
 * writing a `Lowering` block.
 *
 *   node dev/lowering-dump.mts <file.ts> [function]
 *
 * A source the parser refuses has no graph; the command then prints the
 * refusal. */
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import type { Json } from "../tools/calculus.mts";
import { decodeFlowDocument } from "../tools/source-flow.mts";
import { readOutcome, verifier } from "../pipeline/verify-source.mts";
import { runRoot } from "../pipeline/run-directory.mts";

const [file, wanted] = process.argv.slice(2);
if (!file) throw new Error("usage: lowering-dump.mts <file.ts> [function]");
const here = import.meta.dirname;

// The run is written under this command's root, removed when it exits.
runRoot();
// verify-source exits non-zero on a refusal; its outcome is on stdout either way.
const out = spawnSync("node", [join(here, "../pipeline/verify-source.mts"), resolve(file)], { encoding: "utf8" }).stdout;
const outcome = readOutcome(JSON.parse(out.slice(out.indexOf("{"))));
const firstLine = (s: unknown): string => String(s).split("\n")[0] ?? "";
console.log(`outcome: ${outcome.status}${outcome.status === "verified" ? "" : `: ${firstLine(outcome.detail)}`}`);
const fragment = join(outcome.artifacts, "fragment.json");
const lowered = spawnSync(verifier, ["--lower-control-flow", fragment], { encoding: "utf8" });
if (lowered.status !== 0) {
  console.log(firstLine(lowered.stderr));
  process.exit(0);
}
const source = readFileSync(join(outcome.artifacts, "source.ts"), "utf8");
const parsed: Json = JSON.parse(lowered.stdout);
const graphs = decodeFlowDocument(parsed);
/** A span's source text on one line, shortened. */
const text = ([start, end]: readonly [number, number]): string => {
  const t = source.slice(start, end).replace(/\s+/g, " ").trim();
  return t.length > 60 ? `${t.slice(0, 60)}…` : t;
};

for (const g of graphs) {
  const name = text(g.owner);
  if (wanted !== undefined && name !== wanted) continue;
  console.log(`\n${name}:${g.cells.length === 0 ? "" : `  cells ${g.cells.map((c) => c.name).join(", ")}`}`);
  for (const n of g.nodes) {
    const a = n.action;
    const step = a.kind === "end" ? "end"
      : a.kind === "jump" ? `→ n${a.target}`
      : a.kind === "branch" || a.kind === "iteratorStep" ? `if true → n${a.yes}, else → n${a.no}`
      : a.kind === "return" || a.kind === "returnHeld" || a.kind === "rethrow" ? "exit"
      : `→ n${a.next}`;
    const at = "statement" in a ? `  «${text(a.statement)}»` : "binding" in a ? `  ${a.binding.name}` : "";
    const handler = n.handler === null ? "" : `   throws → n${n.handler.target}`;
    console.log(`${n.id === g.entry ? "▸" : " "} n${String(n.id).padEnd(3)} ${a.kind}${at}   ${step}${handler}`);
    for (const e of n.executions) console.log(`        evaluates «${text(e.source)}»`);
  }
}
