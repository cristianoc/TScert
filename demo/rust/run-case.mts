// Rust source cases use the same checker and producer as the demo command.
import { join } from "node:path";
import { front, check } from "./stages.mts";
import type { Outcome } from "../../pipeline/verify-source.mts";

const [name] = process.argv.slice(2);
if (!name || !/^rust-[a-z0-9-]+$/.test(name)) throw Error("expected Rust case name");
const file = join(import.meta.dirname, "examples", `${name}.rs`);
const input = front(file);
let result: Outcome;
if ("refused" in input) result = { status: "unsupported", artifacts: "", phase: "source", detail: input.refused };
else {
  const report = check(file, input.source, input.fragment);
  result = report.status === "verified"
    ? { status: "verified", phase: "check", artifacts: report.artifacts,
        functions: input.fragment.functions.map(f => f.name), initialization: [] }
    : { status: report.status, phase: "search", artifacts: report.artifacts,
        detail: report.detail ?? report.units?.map(u => u.detail).join("\n") ?? "Rust verification failed" };
}
process.stdout.write(JSON.stringify(result) + "\n");
