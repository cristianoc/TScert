#!/usr/bin/env node
/*
 * The axiom check (lean/Verification/Tests/AxiomCheck.lean) checks every safe
 * declaration of the modules it imports. This keeps that set the whole
 * library: every module under lean/Verification is imported by the axiom
 * check, the check itself aside. Lake replays a module whose imports are
 * unchanged, so a module added to the library without its import is caught
 * here, where nothing is replayed.
 */
import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";

const ROOT = "lean";
const CHECK = "Verification.Tests.AxiomCheck";

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

const imported = imports(CHECK);
const library = modules(join(ROOT, "Verification"));
const missing = library.filter(
  (module) => module !== CHECK && !imported.has(module),
);
if (missing.length > 0) {
  process.stderr.write(`${CHECK} does not import ${missing.length} module(s) of the library:\n`);
  for (const module of missing) process.stderr.write(`  ${module}\n`);
  process.exit(1);
}
process.stdout.write(`${CHECK} imports the ${library.length - 1} other modules of the library\n`);
