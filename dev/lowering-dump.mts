/* Prints the program a source function lowers to: the graph the verifier
 * checks, as the verifier itself reports it (`verifier --lower-program`). One
 * line per node: its label, its term, and where control goes next. A record's
 * author starts from this output when writing a `Lowering` block.
 *
 *   node tools/lowering-dump.mts <file.ts> [function]
 *
 * A function the pipeline refuses before the producer's claims exist has no
 * graph; the command then prints the refusal. */
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { join, resolve } from "node:path";
import { showTag, showTerm, unmatched } from "../tools/calculus.mts";
import { decodeNode, type Continuation, type ProgramNode, type Target } from "../tools/control-flow.mts";
import { verifier } from "../pipeline/verify-source.mts";

const [file, wanted] = process.argv.slice(2);
if (!file) throw new Error("usage: lowering-dump.mts <file.ts> [function]");
const here = import.meta.dirname;

// verify-source exits non-zero on a refusal; its outcome is on stdout either way.
const out = spawnSync("node", [join(here, "../pipeline/verify-source.mts"), resolve(file)], { encoding: "utf8" }).stdout;
const outcome = JSON.parse(out.slice(out.indexOf("{")));
const artifacts: string = outcome.artifacts;
const claims = join(artifacts, "claims.json");
const firstLine = (s: unknown) => String(s).split("\n")[0];
console.log(`outcome: ${outcome.status}${outcome.status === "verified" ? "" : `: ${firstLine(outcome.detail)}`}`);
if (!existsSync(claims)) process.exit(0);

const lowered = spawnSync(verifier, ["--lower-program", join(artifacts, "fragment.json"), claims, join(artifacts, "source.ts")], { encoding: "utf8" });
if (lowered.status !== 0) throw new Error(lowered.stderr);

interface Unit { name: string; start: number; program: unknown[]; codes: { arity: number; start: number; program: unknown[] }[] }
// asserted: the verifier's own lowerJson output, whose nodes are decoded below
const units = JSON.parse(lowered.stdout) as Unit[];

const to = (t: Target) => `n${t.label}`;
function showStep(k: Continuation): string {
  switch (k.kind) {
    case "ret": return "return";
    case "bind": return `→ ${to(k.next)}`;
    case "effect": return `→ ${to(k.next)} (value dropped)`;
    case "branch": return `if true → ${to(k.yes)}, else → ${to(k.no)}`;
    case "branchBind": return `if true → ${to(k.yes)}, else → ${to(k.no)} (value kept)`;
    case "tagBind": return `if ${showTag(k.test)} → ${to(k.yes)}, else → ${to(k.no)}`;
    default: return unmatched(k);
  }
}
function printGraph(start: number, program: unknown[]): void {
  const nodes: ProgramNode[] = program.map(decodeNode);
  const width = Math.max(...nodes.map(n => showTerm(n.expression).length));
  nodes.forEach((n, i) => {
    const handler = n.handler ? `   throws → ${to(n.handler)}` : "";
    console.log(`${i === start ? "▸" : " "} n${String(i).padEnd(3)} ${showTerm(n.expression).padEnd(width)}   ${showStep(n.continuation)}${handler}`);
  });
}

for (const u of units.filter(u => wanted === undefined || u.name === wanted)) {
  console.log(`\n${u.name}:`);
  printGraph(u.start, u.program);
  u.codes.forEach((c, i) => {
    console.log(`  code ${i} (${c.arity} parameters):`);
    printGraph(c.start, c.program);
  });
}
