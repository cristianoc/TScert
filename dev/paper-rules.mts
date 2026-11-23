// The experimental prototype of docs/drafts/paper-rules-mode.md over one
// source file: the ordinary check (`pipeline/verify-source.mts`), then the
// paper's annotations (`dev/paper-annotations.mts`) and the pass with the
// rules' layer (`lean/PaperRulesPrototype.lean`, its soundness the axiom
// `paperKeptFactsSurvive`) over the same parsed file. A caller whose written
// instance fails its bound (rule Inst, decided by the annotations script) is
// refused whatever the pass says of it.
//   node dev/paper-rules.mts file.ts [--project dir]
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { check, sourceKey } from "../pipeline/verify-source.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { annotations } from "./paper-annotations.mts";

const prototype = resolve(import.meta.dirname, "../lean/.lake/build/bin/paper-rules-prototype");

/** A unit's verdict line from the prototype. */
interface Verdict { unit: string; accepted?: boolean; acceptedUnderPaperRules?: boolean; assumed?: string; refusal?: string }

function isVerdict(v: unknown): v is Verdict {
  return typeof v === "object" && v !== null && "unit" in v && typeof v.unit === "string";
}

function run(file: string, project: string | undefined): void {
  // The run's directory retained: the prototype reads its parsed file.
  const ordinary = check(file, project === undefined ? undefined : tsconfigOf(project), false, undefined, true,
    { omitted: [], select: null });
  const detail = "detail" in ordinary && typeof ordinary.detail === "string" ? `: ${ordinary.detail.split("\n")[0]?.slice(0, 160) ?? ""}` : "";
  process.stdout.write(`ordinary: ${ordinary.status}${detail}\n`);
  const artifacts = ordinary.artifacts;
  const side = annotations(resolve(file));
  const sidePath = join(artifacts, "paper-side.json");
  writeFileSync(sidePath, JSON.stringify(side));
  const out = execFileSync(prototype, [sidePath, "fragment.json", join("interfaces", "ordinary-interfaces.json"),
    sourceKey(artifacts), "12"], { cwd: artifacts, encoding: "utf8", stdio: ["ignore", "pipe", "ignore"], timeout: 300_000 });
  const failed = new Map(side.calls.filter((c) => !c.ok).map((c) => [c.caller, c.reason ?? "instance"]));
  for (const line of out.split("\n").filter((l) => l.startsWith("{"))) {
    const parsed: unknown = JSON.parse(line);
    if (!isVerdict(parsed)) continue;
    const name = parsed.unit.split("@")[0] ?? parsed.unit;
    const inst = failed.get(name);
    const verdict = inst !== undefined ? `refused: ${inst}`
      : parsed.acceptedUnderPaperRules ? `accepted under the paper's rules (assumes ${parsed.assumed ?? "?"})`
      : parsed.accepted ? "accepted"
      : `refused: ${(parsed.refusal ?? "").split("\n")[0]?.slice(0, 160)}`;
    process.stdout.write(`prototype: ${name}: ${verdict}\n`);
  }
}

if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const args = process.argv.slice(2);
  const at = args.indexOf("--project");
  const project = at < 0 ? undefined : args.splice(at, 2)[1];
  const file = args[0];
  if (file === undefined) {
    process.stderr.write("usage: node dev/paper-rules.mts file.ts [--project dir]\n");
    process.exitCode = 2;
  } else {
    readFileSync(file);
    run(file, project);
  }
}
