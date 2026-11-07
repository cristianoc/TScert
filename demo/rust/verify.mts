// The demo's entry point for one Rust file: its crate through the front end
// and TScert's stages (`stages.mts`). It prints the file's outcome, each
// unit's, and the directory holding what the run wrote.
//
// Usage: node demo/rust/verify.mts <file.rs>

import { check, front, print } from "./stages.mts";

const [file] = process.argv.slice(2);
if (file === undefined) {
  process.stderr.write("usage: node demo/rust/verify.mts <file.rs>\n");
  process.exit(2);
}
const lowered = front(file);
if ("refused" in lowered) {
  process.stdout.write(`unsupported: ${file}\n  ${lowered.refused}\n`);
  process.exit(1);
}
const report = check(file, lowered.source, lowered.fragment);
print(file, report);
process.exit(report.status === "verified" ? 0 : 1);
