#!/usr/bin/env node
/*
 * `verify-source.mts --contracts` names, for each overlay a declaration is
 * read through, the row of the trust surface (DESIGN.md, "Trust surface")
 * stating its trust, by the row's opening words, and the code names its
 * last cell gives. This keeps the table and the rows the same:
 *
 *  1. each overlay's row opens exactly one row of its table, and that row's
 *     last cell names what the overlay says states it;
 *  2. every namespace the reader writes into a declaration identity
 *     (`tscert/<namespace>`, a string or template literal of `tools/`) has
 *     its overlay in `contractNamespaces`, so no stated declaration goes
 *     unplaced.
 */
import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { contractNamespaces, contractOverlays, type ContractOverlay } from "../pipeline/verify-source.mts";

const repo = join(import.meta.dirname, "..");
const design = readFileSync(join(repo, "docs/DESIGN.md"), "utf8");
const start = design.indexOf("\n## Trust surface\n"), end = design.indexOf("\n## ", start + 1);
assert.ok(start >= 0 && end > start, "DESIGN.md has a section Trust surface");
const surface = design.slice(start, end);

/** The rows of each table, by the table's bold heading (`**Assumed values.**`). */
const tables = new Map<string, string[]>();
let table: string[] | null = null;
for (const line of surface.split("\n")) {
  const heading = /^\*\*(.+)\.\*\*/.exec(line);
  if (heading?.[1] !== undefined) tables.set(heading[1], table = []);
  else if (table !== null && line.startsWith("| ") && !line.startsWith("| Assumption |")) table.push(line);
}

const failures: string[] = [];
for (const overlay of Object.keys(contractOverlays).filter((o): o is ContractOverlay => o in contractOverlays)) {
  const { stated, trust } = contractOverlays[overlay];
  const rows = (tables.get(trust.table) ?? []).filter((row) => row.startsWith(`| ${trust.row}`));
  if (rows.length !== 1) {
    failures.push(`${overlay}: ${rows.length} rows of "${trust.table}" open with "${trust.row}"`);
    continue;
  }
  const cells = (rows[0] ?? "").split(" | ");
  const where = cells[cells.length - 1] ?? "";
  for (const name of stated.names)
    if (!where.includes(`\`${name}\``)) failures.push(`${overlay}: the row's last cell does not name \`${name}\``);
  if (stated.in !== null && !where.includes(stated.in)) failures.push(`${overlay}: the row's last cell does not name ${stated.in}`);
}

for (const file of readdirSync(join(repo, "tools")).filter((f) => f.endsWith(".mts"))) {
  const text = readFileSync(join(repo, "tools", file), "utf8");
  for (const match of text.matchAll(/["`]tscert\/([a-z][a-z-]*)/g)) {
    const namespace = match[1] ?? "";
    if (!contractNamespaces.has(namespace)) failures.push(`tools/${file}: the namespace tscert/${namespace} has no overlay`);
  }
}

if (failures.length > 0) {
  process.stderr.write(failures.join("\n") + "\n");
  process.exitCode = 1;
} else {
  process.stdout.write(`${Object.keys(contractOverlays).length} overlays name their trust rows; ${contractNamespaces.size} namespaces placed\n`);
}
