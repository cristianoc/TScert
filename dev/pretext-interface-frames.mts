// node dev/pretext-interface-frames.mts produce <pretext> <bundle> <producer-work>
// node dev/pretext-interface-frames.mts measure <pretext> <bundle> <consumer-work>
import { execFileSync } from "node:child_process";
import { mkdirSync } from "node:fs";
import { join, resolve } from "node:path";
import { initOmission } from "../tools/fragment-parse.mts";
import { object, read } from "./pretext-interface-bundle.mts";

const repo = resolve(import.meta.dirname, "..");
const [mode, source, output, scratch] = process.argv.slice(2);
if (!source || !output || !scratch || (mode !== "produce" && mode !== "measure"))
  throw Error("expected produce|measure <pretext> <bundle> <work>");
const pretext = resolve(source);
const bundle = resolve(output);
const work = resolve(scratch);
mkdirSync(work, { recursive: true });
const head = execFileSync("git", ["-C", pretext, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
const expected = object(object(read(join(repo, "tests/pretext-tier-expected.json")))[head]);

if (mode === "produce") {
  const { produce } = await import("./pretext-interface-produce.mts");
  produce(pretext, bundle, work, Object.keys(expected));
} else {
  const { checkWithInterface, openInterface } = await import("./pretext-interface-check.mts");
  const input = openInterface(bundle);
  let total = 0;
  let accepted = 0;
  for (const [file, record] of Object.entries(expected)) {
    const baseline = Object.entries(object(record))
      .filter(([name, result]) => name !== initOmission && result === "verified").map(([name]) => name);
    total += baseline.length;
    const { passed, used, detail, refusals } = checkWithInterface(join(pretext, "src", file), input, work);
    const lost = baseline.filter((name) => !passed.has(name));
    const count = baseline.length - lost.length;
    accepted += count;
    if (detail) {
      console.log(`${file}: 0/${baseline.length}, ${detail.split("\n")[0]}`);
      continue;
    }
    console.log(`${file}: ${count}/${baseline.length}, contracts [${used.join(", ")}]`);
    for (const name of lost) console.log(`  missing ${name}: ${refusals.get(name) ?? "no verdict"}`);
  }
  console.log(`Pretext: ${accepted}/${total} previously verified functions retained`);
}
