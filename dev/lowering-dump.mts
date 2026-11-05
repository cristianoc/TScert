/* Prints the program a source function lowers to: the graph the verifier
 * checks, as the verifier itself reports it (`verifier --lower-program`). One
 * line per node: its label, its term, and where control goes next. A record's
 * author starts from this output when writing a `Lowering` block.
 *
 *   node dev/lowering-dump.mts <file.ts> [function]
 *
 * A function the pipeline refuses before the producer's claims exist has no
 * graph; the command then prints the refusal. */
import { spawnSync } from "node:child_process";
import { present } from "../tools/files.mts";
import { join, resolve } from "node:path";
import { fields, nat, showTag, showTerm, unmatched, type Json } from "../tools/calculus.mts";
import { decodeNode, type Continuation, type ProgramNode, type Target } from "../tools/control-flow.mts";
import { readOutcome, sourceKey, verifier } from "../pipeline/verify-source.mts";
import { runRoot } from "../pipeline/run-directory.mts";

const [file, wanted] = process.argv.slice(2);
if (!file) throw new Error("usage: lowering-dump.mts <file.ts> [function]");
const here = import.meta.dirname;

// The run is written under this command's root, removed when it exits.
runRoot();
// verify-source exits non-zero on a refusal; its outcome is on stdout either way.
const out = spawnSync("node", [join(here, "../pipeline/verify-source.mts"), resolve(file)], { encoding: "utf8" }).stdout;
const outcome = readOutcome(JSON.parse(out.slice(out.indexOf("{"))));
const artifacts: string = outcome.artifacts;
const claims = join(artifacts, "claims.json");
const firstLine = (s: unknown): string => String(s).split("\n")[0];
console.log(`outcome: ${outcome.status}${outcome.status === "verified" ? "" : `: ${firstLine(outcome.detail)}`}`);
if (!present(claims)) process.exit(0);

const lowered = spawnSync(verifier, ["--lower-program", join(artifacts, "fragment.json"), claims, sourceKey(artifacts)], { encoding: "utf8" });
if (lowered.status !== 0) throw new Error(lowered.stderr);

interface Unit { name: string; start: number; program: Json[]; codes: { arity: number; start: number; program: Json[] }[] }
/** The verifier's lowerJson output: per unit its name, entry node and nodes,
 * and per code its arity, entry node and nodes; the nodes are decoded where
 * they are printed. */
function decodeUnits(v: Json): Unit[] {
  if (!Array.isArray(v)) throw Error("invalid lowering: units expected");
  return v.map((u: Json): Unit => {
    const o = fields(u, ["name", "start", "program", "codes"]);
    const name = o.name, program = o.program, codes = o.codes;
    if (typeof name !== "string" || !Array.isArray(program) || !Array.isArray(codes)) throw Error("invalid lowering unit");
    return { name, start: nat(o.start), program, codes: codes.map((c: Json) => {
      const k = fields(c, ["arity", "start", "program"]);
      const nodes = k.program;
      if (!Array.isArray(nodes)) throw Error("invalid lowering code");
      return { arity: nat(k.arity), start: nat(k.start), program: nodes };
    }) };
  });
}
const units = decodeUnits(JSON.parse(lowered.stdout));

const to = (t: Target): string => `n${t.label}`;
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
function printGraph(start: number, program: Json[]): void {
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
