// Standalone release-profile probe; this checks rustc behavior, not translation faithfulness.
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const dir = mkdtempSync(join(tmpdir(), "tscert-i64-release-"));
const source = join(dir, "probe.rs"), binary = join(dir, "probe");
writeFileSync(source, readFileSync(join(import.meta.dirname, "examples/i64.rs"), "utf8") + `
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let x: i64 = args[2].parse().unwrap();
    let y: i64 = args[3].parse().unwrap();
    let result = match args[1].as_str() {
        "mul" => product(x, y), "div" => quotient(x, y),
        "rem" => remainder(x, y), "neg" => negate(x), _ => identity(x),
    };
    println!("{}", result);
}
`);
const built = spawnSync("rustc", ["-O", "-C", "overflow-checks=off", "-C", "panic=abort", source, "-o", binary], { encoding: "utf8" });
if (built.error || built.status !== 0) throw Error(built.error?.message ?? built.stderr);
const examples: readonly (readonly [string, string, string, string | null])[] = [
  ["mul", "9223372036854775807", "2", "-2"],
  ["neg", "-9223372036854775808", "0", "-9223372036854775808"],
  ["div", "-7", "3", "-2"], ["rem", "-7", "3", "-1"],
  ["div", "1", "0", null], ["rem", "1", "0", null],
  ["div", "-9223372036854775808", "-1", null],
  ["rem", "-9223372036854775808", "-1", null],
];
for (const [op, x, y, result] of examples) {
  const ran = spawnSync(binary, [op, x, y], { encoding: "utf8" });
  if (ran.error) throw ran.error;
  if (result === null ? ran.status === 0 : ran.status !== 0 || ran.stdout.trim() !== result)
    throw Error(`${op}(${x}, ${y}): ${ran.stdout} ${ran.stderr}`);
  process.stdout.write(`${op}(${x}, ${y}): ${result ?? "panicked"}\n`);
}
process.stdout.write(`artifacts: ${dir}\n`);
