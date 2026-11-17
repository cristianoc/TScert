#!/usr/bin/env node
/*
 * Each axiom check checks every safe declaration of the modules it imports
 * within its part of the library: lean/Verification/Tests/AxiomCheck.lean the
 * modules outside Verification.Paper, and
 * lean/Verification/Paper/TolerantFrames/Tests/AxiomCheck.lean those under it.
 * This keeps each set its whole part: every module of a part is imported by
 * that part's check, the check itself aside. Lake replays a module whose
 * imports are unchanged, so a module added without its import is caught here,
 * where nothing is replayed.
 */
import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";

const ROOT = "lean";
const PAPER = "Verification.Paper.";

/** The two parts of the library, each with its check. */
const PARTS: readonly { check: string; owns: (module: string) => boolean }[] = [
  { check: "Verification.Tests.AxiomCheck", owns: (module) => !module.startsWith(PAPER) },
  { check: "Verification.Paper.TolerantFrames.Tests.AxiomCheck", owns: (module) => module.startsWith(PAPER) },
];

function modules(dir: string): string[] {
  return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) return modules(path);
    if (!entry.name.endsWith(".lean")) return [];
    return [relative(ROOT, path).slice(0, -".lean".length).split("/").join(".")];
  });
}

function imports(module: string): Set<string> {
  const text = readFileSync(join(ROOT, ...module.split(".")) + ".lean", "utf8");
  return new Set([...text.matchAll(/^import\s+(\S+)/gm)].map((m) => m[1] ?? ""));
}

const library = modules(join(ROOT, "Verification"));
let failed: boolean = false;
for (const { check, owns } of PARTS) {
  const imported = imports(check);
  const part = library.filter((module) => owns(module) && module !== check);
  const missing = part.filter((module) => !imported.has(module));
  if (missing.length > 0) {
    failed = true;
    process.stderr.write(`${check} does not import ${missing.length} module(s) of its part:\n`);
    for (const module of missing) process.stderr.write(`  ${module}\n`);
  } else {
    process.stdout.write(`${check} imports the ${part.length} other modules of its part\n`);
  }
}
if (failed) process.exit(1);
