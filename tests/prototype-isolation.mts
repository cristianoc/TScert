#!/usr/bin/env node
/*
 * Keeps the disposable paper-rules prototype (`dev/paper-annotations.mts`,
 * `dev/paper-rules.mts`, `lean/PaperRulesPrototype.lean`) isolated from the
 * proved verifier (`tools/`, `pipeline/`, `lean/Verification/`, `lean/Main.lean`)
 * and marked for deletion upon unification.
 */
import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";

const PROTOTYPE_FILES: readonly string[] = [
  "dev/paper-annotations.mts",
  "dev/paper-rules.mts",
  "lean/PaperRulesPrototype.lean",
];

const MARKER: string = "PROTOTYPE ONLY";

function walk(dir: string, ext: string): string[] {
  return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    if (entry.name === "node_modules" || entry.name === ".lake") return [];
    const path = join(dir, entry.name);
    if (entry.isDirectory()) return walk(path, ext);
    return entry.name.endsWith(ext) ? [path] : [];
  });
}

const problems: string[] = [];

for (const file of PROTOTYPE_FILES) {
  const head = readFileSync(file, "utf8").slice(0, 600);
  if (!head.includes(MARKER)) {
    problems.push(`${file}: missing "${MARKER}" isolation banner at top of file`);
  }
}

const tsDirs: readonly string[] = ["tools", "pipeline"];
const tsForbidden: readonly RegExp[] = [
  /\bfrom\s+["'][^"']*paper-(?:annotations|rules)(?:\.mts)?["']/,
  /\bimport\s*\(\s*["'][^"']*paper-(?:annotations|rules)(?:\.mts)?["']/,
  /\bpaper-rules-prototype\b/,
];

let tsCount: number = 0;
for (const dir of tsDirs) {
  for (const file of walk(dir, ".mts")) {
    tsCount += 1;
    const text = readFileSync(file, "utf8");
    for (const pat of tsForbidden) {
      if (pat.test(text)) {
        problems.push(`${relative(".", file)}: references disposable paper-rules prototype (${pat.source})`);
      }
    }
  }
}

const leanFiles = [...walk(join("lean", "Verification"), ".lean"), join("lean", "Main.lean")];
const leanForbidden: readonly RegExp[] = [/^import\s+PaperRulesPrototype\b/m, /\bpaperKeptFactsSurvive\b/];

for (const file of leanFiles) {
  const text = readFileSync(file, "utf8");
  for (const pat of leanForbidden) {
    if (pat.test(text)) {
      problems.push(`${relative(".", file)}: references disposable paper-rules prototype (${pat.source})`);
    }
  }
}

if (problems.length > 0) {
  for (const p of problems) process.stderr.write(`${p}\n`);
  process.exit(1);
}
process.stdout.write(
  `prototype-isolation: ${tsCount} TS modules and ${leanFiles.length} Lean modules clean; ${PROTOTYPE_FILES.length} prototype files marked\n`,
);
