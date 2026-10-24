// The census of the front end's own functions (WORK.md, "The front end's own
// functions"): each top-level function of a directory's modules sliced into a
// file of its own, with the same-file declarations it uses and the imports
// they name, and each slice run through the pipeline, in the directory's
// copy beside a copy of tools/. Each run writes a census record (DESIGN.md,
// "The stage store"): per slice its source identity, outcome and the
// ordered references to its stage invocations with their elapsed and CPU
// times and peak memory. `report` and the end of a run print each stage's
// cost, CPU time first, and the slices that cost the most CPU.
// Processes split the slices with `--shard i/n` and share the stage store.
//   node dev/census.mts [--dir tools] [--files a.mts,…] [--functions f,…] [--shard i/n]
//       [--out dir] [--record file]
//   node dev/census.mts report <before.json[,shard.json…]> <after.json[,shard.json…]>
//   node dev/census.mts report <record.json[,shard.json…]> [--per-function]
//   node dev/census.mts coverage <record.json[,shard.json…]> [--per-function] [--sources checkout|commit]
// A record also holds the directory's statement inventory, each statement
// classified by its function's outcome (statement-coverage.mts); `report`
// and the end of a run print verified statement coverage, and `coverage`
// computes it for a record from the sources of the record's commit (of the
// checkout for a census of a dirty tree, or by `--sources`), without
// running a slice.
// The step limit is TSCERT_STEP_LIMIT's, the store TSCERT_STAGE_STORE's.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, statSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, relative, resolve } from "node:path";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";
import { checkApart, invocationLog, stepTimeoutMs } from "../pipeline/verify-source.mts";
import { readInvocationLog, storeSetting, type AttemptRecord, type Cpu } from "../pipeline/stages.mts";
import { stageNames, type StageName } from "../pipeline/stage-execution.mts";
import { runRoot } from "../pipeline/run-directory.mts";
import { classify, coverageComparison, coverageReport, inventory, type Unit, type UnitRecord, type UnitScope }
  from "./statement-coverage.mts";

const repository = resolve(import.meta.dirname, "..");
const sha256 = (text: string): string => createHash("sha256").update(text).digest("hex");

/** One slice: its file, the function it holds, and its text. */
type Slice = { slice: string; file: string; fn: string; text: string };

/** A slice's stage invocation, as the census keeps it after its artifacts
 * and the store's entries are gone. */
type InvocationReference = {
  attempt: string;
  stage: StageName;
  key: string | null;
  execution: AttemptRecord["execution"];
  limitMs: number | null;
  elapsedMs: number;
  cpu: Cpu;
  /** For a replay, the stored attempt's limit and elapsed time, and the
   * replay's own lookup, validation and materialization. */
  replay: { storedAttempt: string; storedLimitMs: number | null; storedElapsedMs: number; lookupMs: number;
    validationMs: number; materializationMs: number } | null;
};
type SliceRecord = {
  slice: string;
  file: string;
  fn: string;
  lines: number;
  sourceSha256: string;
  status: string;
  phase: string;
  /** The outcome's first line. */
  detail: string;
  functions: number;
  invocations: InvocationReference[];
  /** The bytes of each JSON document the slice's run wrote (the Fragment,
   * the claims, the evidence), by file name; null where the record predates
   * them or the run wrote none. */
  artifactBytes: { [name: string]: number } | null;
};
type CensusRecord = {
  source: { commit: string; dirty: boolean; directory: string; files: string[] | null; functions: string[] | null };
  policy: { store: string; stepLimitMs: number; shard: [number, number] | null };
  started: string;
  elapsedMs: number;
  slices: SliceRecord[];
  /** The statements of the census's files, each with its class by this
   * record's slices, and each file's source hash. */
  inventory: { files: { file: string; sourceSha256: string }[]; units: UnitRecord[] };
};

// ---------------------------------------------------------------------------
// Slicing

/** Every identifier a node's subtree spells. */
function identifiers(node: ts.Node, into: Set<string>): Set<string> {
  const visit = (n: ts.Node): void => {
    if (ts.isIdentifier(n)) into.add(n.text);
    n.forEachChild(visit);
  };
  visit(node);
  return into;
}

/** The slices of one module: each function declaration with a body and a
 * name, with the module's declarations it uses, transitively, in the
 * module's order, and the imports of the names they use. */
function slicesOf(file: string, tree: ts.SourceFile, text: string): Slice[] {
  const declarations = new Map<string, ts.Statement>();
  const imports: ts.ImportDeclaration[] = [];
  for (const s of tree.statements) {
    if (ts.isImportDeclaration(s)) {
      imports.push(s);
      continue;
    }
    const names: string[] = [];
    if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isInterfaceDeclaration(s) ||
        ts.isTypeAliasDeclaration(s) || ts.isEnumDeclaration(s)) && s.name)
      names.push(s.name.text);
    if (ts.isVariableStatement(s))
      for (const d of s.declarationList.declarations) if (ts.isIdentifier(d.name)) names.push(d.name.text);
    for (const n of names) declarations.set(n, s);
  }
  const slices: Slice[] = [];
  for (const s of tree.statements) {
    if (!ts.isFunctionDeclaration(s) || !s.name || !s.body) continue;
    const needed = new Set<ts.Node>([s]);
    const used = new Set<string>();
    for (let work: ts.Node[] = [s], next = work.pop(); next !== undefined; next = work.pop())
      for (const id of identifiers(next, new Set())) {
        used.add(id);
        const d = declarations.get(id);
        if (d && !needed.has(d)) {
          needed.add(d);
          work.push(d);
        }
      }
    const parts: string[] = [];
    for (const im of imports) {
      const clause = im.importClause;
      if (!clause) continue;
      const specifier = text.slice(im.moduleSpecifier.pos, im.moduleSpecifier.end).trim();
      if (clause.name && used.has(clause.name.text)) parts.push(text.slice(im.pos, im.end).trim());
      const bindings = clause.namedBindings;
      if (bindings && ts.isNamespaceImport(bindings) && used.has(bindings.name.text))
        parts.push(text.slice(im.pos, im.end).trim());
      if (bindings && ts.isNamedImports(bindings)) {
        const elements = bindings.elements.filter((e) => used.has(e.name.text)).map((e) => text.slice(e.pos, e.end).trim());
        const typeOnly = clause.phaseModifier === ts.SyntaxKind.TypeKeyword;
        if (elements.length) parts.push(`import ${typeOnly ? "type " : ""}{ ${elements.join(", ")} } from ${specifier};`);
      }
    }
    for (const st of tree.statements)
      if (needed.has(st)) {
        let source = text.slice(st.getStart(tree), st.end).trim();
        if (st === s && !/^export\b/.test(source)) source = "export " + source;
        parts.push(source);
      }
    slices.push({ slice: `slice-${file.replace(/\.mts$/, "")}-${s.name.text}.mts`, file, fn: s.name.text,
      text: parts.join("\n\n") + "\n" });
  }
  return slices;
}

// ---------------------------------------------------------------------------
// The census's directory

/** Write `text` at `path` unless it holds it already, by rename: a process
 * sharing the directory reads the old file or the new one, never a part. */
function writeStable(path: string, text: string): void {
  if (existsSync(path) && readFileSync(path, "utf8") === text) return;
  const temporary = `${path}.${process.pid}.tmp`;
  writeFileSync(temporary, text);
  renameSync(temporary, path);
}

/** The census's copy of tools/, `directory` and their local import closure,
 * with tools/'s installation linked, at a path the same for every process and run of
 * this checkout, so slices' module paths, and the stage keys embedding them,
 * repeat. */
function prepare(out: string, directory: string): void {
  const copy = (from: string, to: string, select: (name: string) => boolean): void => {
    mkdirSync(to, { recursive: true });
    const names = new Set(readdirSync(from).filter(select).sort());
    for (const name of readdirSync(to).filter(select))
      if (!names.has(name) && !name.startsWith("slice-")) rmSync(join(to, name), { force: true });
    for (const name of names)
      writeStable(join(to, name), readFileSync(join(from, name), "utf8"));
  };
  copy(join(repository, "tools"), join(out, "tools"),
    (n) => n.endsWith(".mts") || n.endsWith(".d.ts") || n === "tsconfig.json");
  const installation = join(out, "tools", "node_modules");
  if (!existsSync(installation)) {
    try {
      symlinkSync(join(repository, "tools", "node_modules"), installation);
    } catch (error) {
      if (!(error instanceof Error && "code" in error && error.code === "EEXIST")) throw error;
    }
  }
  if (directory !== "tools") copy(join(repository, directory), join(out, directory), (n) => n.endsWith(".mts"));
  const seen = new Set<string>();
  const work = [...new Set(["tools", directory])].flatMap((dir) =>
    readdirSync(join(repository, dir)).filter((n) => n.endsWith(".mts") || n.endsWith(".d.ts"))
      .map((n) => join(repository, dir, n)));
  for (let path = work.pop(); path !== undefined; path = work.pop()) {
    if (seen.has(path)) continue;
    seen.add(path);
    const text = readFileSync(path, "utf8");
    const target = join(out, relative(repository, path));
    mkdirSync(dirname(target), { recursive: true });
    writeStable(target, text);
    const from = dirname(path);
    const add = (specifier: ts.Node | undefined): void => {
      if (specifier && ts.isStringLiteral(specifier) && specifier.text.startsWith("."))
        work.push(resolve(from, specifier.text));
    };
    const visit = (node: ts.Node): void => {
      if (ts.isImportDeclaration(node) || ts.isExportDeclaration(node)) add(node.moduleSpecifier);
      if (ts.isCallExpression(node) && node.expression.kind === ts.SyntaxKind.ImportKeyword) add(node.arguments[0]);
      if (ts.isImportTypeNode(node) && ts.isLiteralTypeNode(node.argument)) add(node.argument.literal);
      node.forEachChild(visit);
    };
    visit(openText(path, text));
  }
}

// ---------------------------------------------------------------------------
// Running

/** A census option's value. */
function option(args: string[], name: string): string | null {
  const at = args.indexOf(name);
  if (at < 0) return null;
  const value = args[at + 1];
  if (value === undefined) throw Error(`${name} needs a value`);
  args.splice(at, 2);
  return value;
}

function reference(r: AttemptRecord): InvocationReference {
  return {
    attempt: r.attempt, stage: r.stage, key: r.key, execution: r.execution, limitMs: r.limitMs, elapsedMs: r.elapsedMs,
    cpu: r.cpu,
    replay: r.replay && { storedAttempt: r.replay.stored.attempt, storedLimitMs: r.replay.stored.limitMs,
      storedElapsedMs: r.replay.stored.elapsedMs,
      lookupMs: r.replay.lookupMs, validationMs: r.replay.validationMs, materializationMs: r.replay.materializationMs },
  };
}

/** The invocations of the run that checked `source`, found by its request
 * in the run root: for a run whose worker died before its outcome. */
function invocationsOfRequest(source: string): InvocationReference[] {
  const root = runRoot();
  for (const name of readdirSync(root).filter((n) => n.startsWith("pipeline-"))) {
    const request = join(root, name, "request.json");
    if (!existsSync(request)) continue;
    const parsed: unknown = JSON.parse(readFileSync(request, "utf8"));
    if (typeof parsed === "object" && parsed !== null && "source" in parsed && parsed.source === source)
      return readInvocationLog(join(root, name, invocationLog)).map(reference);
  }
  return [];
}

async function census(args: string[]): Promise<void> {
  const directory = option(args, "--dir") ?? "tools";
  const files = option(args, "--files")?.split(",") ?? null;
  const functions = option(args, "--functions")?.split(",") ?? null;
  const shardText = option(args, "--shard");
  const shard = shardText === null ? null : /^(\d+)\/(\d+)$/.exec(shardText);
  if (shardText !== null && (!shard || Number(shard[1]) < 1 || Number(shard[1]) > Number(shard[2])))
    throw Error(`--shard takes i/n with 1 ≤ i ≤ n: ${shardText}`);
  const out = resolve(option(args, "--out") ??
    join(tmpdir(), "tscert-census", sha256(repository).slice(0, 12), directory));
  const shardPart: [number, number] | null = shard ? [Number(shard[1]), Number(shard[2])] : null;
  const commit = execFileSync("git", ["-C", repository, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
  const dirty = execFileSync("git", ["-C", repository, "status", "--porcelain", "--", "tools", directory, "pipeline"],
    { encoding: "utf8" }).trim() !== "";
  const recordPath = resolve(option(args, "--record") ??
    join(out, "..", `census-${directory}-${commit.slice(0, 12)}-${new Date().toISOString().replace(/[:.]/g, "-")}${
      shardPart ? `-${shardPart[0]}-of-${shardPart[1]}` : ""}.json`));
  if (args.length) throw Error(`unknown arguments: ${args.join(" ")}`);

  const started = performance.now();
  prepare(out, directory);
  const root = join(out, directory);
  const all: Slice[] = [];
  const units: Unit[] = [];
  const fileHashes: { file: string; sourceSha256: string }[] = [];
  for (const file of readdirSync(join(repository, directory)).filter((f) => f.endsWith(".mts") && !f.startsWith("slice-")).sort()) {
    if (files && !files.includes(file)) continue;
    const text = readFileSync(join(root, file), "utf8");
    const tree = openText(join(root, file), text);
    all.push(...slicesOf(file, tree, text));
    units.push(...inventory(file, tree));
    fileHashes.push({ file, sourceSha256: sha256(text) });
  }
  closeParser();
  // Functions whose slices have one text (a mutually recursive group) share one slice file, the first's, and its
  // one check (STAGE-STORE.md, "Shared work").
  const named = new Map<string, string>();
  for (const s of all) if (!named.has(s.text)) named.set(s.text, s.slice);
  const shared = all.map((s): Slice => ({ ...s, slice: named.get(s.text) ?? s.slice }));
  const chosen = functions ? shared.filter((s) => functions.includes(s.fn)) : shared;
  // A slice file no function of the directory has any longer is removed; one a narrower census does not choose
  // stays, so a census of some files or functions leaves a concurrent census's slices in place.
  if (files === null) {
    const sliceNames = new Set(shared.map((s) => s.slice));
    for (const name of readdirSync(root))
      if (name.startsWith("slice-") && name.endsWith(".mts") && !sliceNames.has(name))
        rmSync(join(root, name), { force: true });
  }
  for (const s of chosen) writeStable(join(root, s.slice), s.text);
  // A shard takes every n-th slice file, with every function sharing it: one text is checked in one shard.
  const sliceFiles = [...new Set(chosen.map((s) => s.slice))];
  const selected = shardPart
    ? chosen.filter((s) => sliceFiles.indexOf(s.slice) % shardPart[1] === shardPart[0] - 1) : chosen;
  process.stderr.write(`${selected.length} of ${all.length} slices\n`);

  const project = join(out, "tools");
  // Progress: the slices' outcomes and their stages' executions so far.
  let finished = 0;
  const outcomes = new Map<string, number>();
  const executions = new Map<string, number>();
  const bump = (m: Map<string, number>, k: string): void => void m.set(k, (m.get(k) ?? 0) + 1);
  const tally = (m: Map<string, number>): string => [...m].map(([k, n]) => `${k} ${n}`).join(", ");
  const sliceRow = async (s: Slice): Promise<SliceRecord> => {
    const path = join(root, s.slice);
    const base = { slice: s.slice, file: s.file, fn: s.fn, lines: s.text.split("\n").length,
      sourceSha256: createHash("sha256").update(s.text).digest("hex") };
    try {
      const o = await checkApart(path, project);
      return { ...base, status: o.status, phase: o.phase, detail: o.status === "verified" ? "" : o.detail.split("\n")[0],
        functions: o.status === "verified" ? o.functions.length : 0,
        invocations: readInvocationLog(join(o.artifacts, invocationLog)).map(reference),
        artifactBytes: documentBytes(o.artifacts) };
    } catch (error) {
      return { ...base, status: "error", phase: "-", detail: String(error).split("\n")[0], functions: 0,
        invocations: invocationsOfRequest(path), artifactBytes: null };
    }
  };
  const finish = async (s: Slice): Promise<SliceRecord> => {
    const row = await sliceRow(s);
    finished++;
    bump(outcomes, row.detail.startsWith("timeout:") ? "timeout" : row.status);
    for (const i of row.invocations) bump(executions, i.execution);
    if (finished % 10 === 0 || finished === selected.length)
      process.stderr.write(`${finished} of ${selected.length} slices, ${((performance.now() - started) / 1000).toFixed(0)} s` +
        ` · ${tally(outcomes)} · stages ${tally(executions)}\n`);
    return row;
  };
  // Slices of one text (the functions of one mutually recursive group) share one check, the first's: each other
  // function's row holds its outcome and no invocation of its own; groups run in parallel.
  const groups = new Map<string, Slice[]>();
  for (const s of selected) {
    const text = createHash("sha256").update(s.text).digest("hex");
    const group = groups.get(text);
    if (group) group.push(s);
    else groups.set(text, [s]);
  }
  const done = new Map<Slice, SliceRecord>();
  await Promise.all([...groups.values()].map(async ([first, ...rest]): Promise<void> => {
    if (!first) return;
    const row = await finish(first);
    done.set(first, row);
    for (const s of rest) {
      done.set(s, { ...row, file: s.file, fn: s.fn, invocations: [] });
      finished++;
    }
  }));
  const rows = selected.map((s): SliceRecord => {
    const row = done.get(s);
    if (!row) throw Error(`no outcome for ${s.slice}`);
    return row;
  });
  const setting = storeSetting();
  const sliceOutcomes = bySlice(rows);
  const record: CensusRecord = {
    source: { commit, dirty, directory, files, functions },
    policy: { store: setting.off ? "off" : setting.directory, stepLimitMs: stepTimeoutMs, shard: shardPart },
    started: new Date(Date.now() - (performance.now() - started)).toISOString(),
    elapsedMs: performance.now() - started,
    slices: rows,
    inventory: { files: fileHashes, units: units.map((u) => ({ ...u, class: classify(u, sliceOutcomes) })) },
  };
  writeFileSync(recordPath, JSON.stringify(record, null, 1) + "\n");
  summarize(record.slices);
  process.stdout.write(costReport(record.slices));
  process.stdout.write(coverageReport(directory, record.inventory.units, sliceOutcomes, false));
  process.stdout.write(`record: ${recordPath}\n`);
}

/** A detail without its line, column and span: the blocker it names. */
const blocker = (detail: string): string =>
  detail.replace(/\(line \d+, col \d+\)/, "").replace(/ at \[\d+,\d+\).*/, "").slice(0, 140);

function summarize(slices: readonly SliceRecord[]): void {
  const counts: Record<string, number> = {};
  for (const s of slices) counts[`${s.status}/${s.phase}`] = (counts[`${s.status}/${s.phase}`] ?? 0) + 1;
  process.stdout.write(`slices: ${slices.length} ${JSON.stringify(counts)}\n`);
  const blockers = new Map<string, number>();
  for (const s of slices.filter((s) => s.status !== "verified"))
    blockers.set(blocker(s.detail), (blockers.get(blocker(s.detail)) ?? 0) + 1);
  for (const [b, n] of [...blockers].sort((a, b) => b[1] - a[1])) process.stdout.write(`${String(n).padStart(4)} ${b}\n`);
  process.stdout.write(`verified: ${slices.filter((s) => s.status === "verified").map((s) => `${s.file}#${s.fn}`).join(", ")}\n`);
}

// ---------------------------------------------------------------------------
// Cost: CPU time first, elapsed time second, peak memory

/** What an invocation's result cost: the CPU time, elapsed time and peak
 * memory of the execution that produced it, this attempt's own or, for a
 * replay, the stored execution's; null where it is not measured. */
type Cost = { cpuMs: number | null; elapsedMs: number; peakBytes: number | null };
function cost(r: InvocationReference): Cost {
  const measured = "userMs" in r.cpu ? r.cpu : null;
  return { cpuMs: measured ? measured.userMs + measured.systemMs : null,
    elapsedMs: r.replay ? r.replay.storedElapsedMs : r.elapsedMs, peakBytes: measured?.peakBytes ?? null };
}
const ran = (r: InvocationReference): boolean => r.execution === "executed" || r.execution === "timed-out" ||
  r.execution === "failed";

/** A distribution's total, median, 90th percentile and maximum, and how many
 * values are missing. */
type Spread = { n: number; missing: number; total: number; median: number; p90: number; max: number };
function spread(values: readonly (number | null)[]): Spread {
  const known = values.filter((v): v is number => v !== null).sort((a, b) => a - b);
  const at = (q: number): number => known.length ? known[Math.min(known.length - 1, Math.ceil(q * known.length) - 1)] : 0;
  return { n: known.length, missing: values.length - known.length, total: known.reduce((a, b) => a + b, 0),
    median: at(0.5), p90: at(0.9), max: known.at(-1) ?? 0 };
}
/** Milliseconds as seconds, or n/a where none is known; a partial total
 * names how many are missing. */
function seconds(s: Spread, field: "total" | "median" | "p90" | "max"): string {
  if (s.n === 0) return "n/a";
  return (s[field] / 1000).toFixed(field === "total" ? 1 : 2) + (field === "total" && s.missing ? `+${s.missing}n/a` : "");
}
const megabytes = (s: Spread, field: "median" | "p90" | "max"): string =>
  s.n === 0 ? "n/a" : (s[field] / 1048576).toFixed(0);

/** Each stage's cost over a census's invocations: CPU, then elapsed, then
 * peak memory; and the slices that cost the most CPU. */
function costReport(slices: Iterable<SliceRecord>, top: number = 10): string {
  const rows = [...slices];
  const byStage = new Map<StageName, InvocationReference[]>();
  for (const s of rows) for (const r of s.invocations) byStage.set(r.stage, [...(byStage.get(r.stage) ?? []), r]);
  const lines = ["stage cost (each result's producing execution; seconds, peak MB):",
    `  ${"stage".padEnd(12)} ${"ran".padStart(5)} ${"replay".padStart(6)} │ ${"CPU".padStart(10)} ${"med".padStart(6)} ` +
    `${"p90".padStart(6)} ${"max".padStart(7)} │ ${"elapsed".padStart(10)} ${"med".padStart(6)} ${"p90".padStart(6)} ` +
    `${"max".padStart(7)} │ ${"peak med".padStart(8)} ${"p90".padStart(5)} ${"max".padStart(5)}`];
  for (const [stage, invocations] of [...byStage].sort((a, b) =>
    spread(b[1].map((r) => cost(r).cpuMs)).total - spread(a[1].map((r) => cost(r).cpuMs)).total)) {
    const costs = invocations.map(cost);
    const c = spread(costs.map((x) => x.cpuMs)), e = spread(costs.map((x) => x.elapsedMs));
    const m = spread(costs.map((x) => x.peakBytes));
    lines.push(`  ${stage.padEnd(12)} ${String(invocations.filter(ran).length).padStart(5)} ` +
      `${String(invocations.filter((r) => !ran(r)).length).padStart(6)} │ ${seconds(c, "total").padStart(10)} ` +
      `${seconds(c, "median").padStart(6)} ${seconds(c, "p90").padStart(6)} ${seconds(c, "max").padStart(7)} │ ` +
      `${seconds(e, "total").padStart(10)} ${seconds(e, "median").padStart(6)} ${seconds(e, "p90").padStart(6)} ` +
      `${seconds(e, "max").padStart(7)} │ ${megabytes(m, "median").padStart(8)} ${megabytes(m, "p90").padStart(5)} ` +
      `${megabytes(m, "max").padStart(5)}`);
  }
  const perSlice = rows.map((s) => {
    const costs = s.invocations.map(cost);
    return { s, cpu: spread(costs.map((x) => x.cpuMs)), elapsed: spread(costs.map((x) => x.elapsedMs)),
      peak: spread(costs.map((x) => x.peakBytes)),
      bytes: s.artifactBytes ? Object.values(s.artifactBytes).reduce((a, b) => a + b, 0) : null };
  });
  lines.push(`slices by CPU (top ${Math.min(top, perSlice.length)}; seconds, peak MB, document bytes):`);
  for (const { s, cpu, elapsed, peak, bytes } of perSlice.sort((a, b) => b.cpu.total - a.cpu.total).slice(0, top))
    lines.push(`  ${seconds(cpu, "total").padStart(10)} CPU ${seconds(elapsed, "total").padStart(8)} elapsed ` +
      `${megabytes(peak, "max").padStart(5)} MB ${String(bytes ?? "n/a").padStart(9)} B  ${s.file}#${s.fn} ` +
      `${isTimeout(s) ? "timeout" : `${s.status}/${s.phase}`}`);
  return lines.join("\n") + "\n";
}

// ---------------------------------------------------------------------------
// Records read back, and compared

/** The bytes of each JSON document in a run's directory, by file name. */
function documentBytes(directory: string): { [name: string]: number } {
  const bytes: { [name: string]: number } = {};
  for (const name of readdirSync(directory).filter((n) => n.endsWith(".json")).sort())
    bytes[name] = statSync(join(directory, name)).size;
  return bytes;
}
function readArtifactBytes(value: unknown): SliceRecord["artifactBytes"] {
  if (value === undefined || value === null) return null;
  if (typeof value !== "object") throw Error("artifactBytes is not a record");
  const bytes: { [name: string]: number } = {};
  for (const [name, n] of Object.entries(value)) {
    if (typeof n !== "number") throw Error(`artifactBytes.${name} is not a number`);
    bytes[name] = n;
  }
  return bytes;
}
function readSliceRecord(value: unknown): SliceRecord {
  if (typeof value !== "object" || value === null) throw Error("not a slice record");
  const v: { [key: string]: unknown } = { ...value };
  const { slice, file, fn, lines, sourceSha256, status, phase, detail, functions, invocations, artifactBytes } = v;
  if (typeof slice !== "string" || typeof file !== "string" || typeof fn !== "string" || typeof lines !== "number" ||
      typeof sourceSha256 !== "string" || typeof status !== "string" || typeof phase !== "string" ||
      typeof detail !== "string" || typeof functions !== "number" || !Array.isArray(invocations))
    throw Error(`not a slice record: ${JSON.stringify(value).slice(0, 200)}`);
  return { slice, file, fn, lines, sourceSha256, status, phase, detail, functions,
    invocations: invocations.map(readReference), artifactBytes: readArtifactBytes(artifactBytes) };
}
function readReference(value: unknown): InvocationReference {
  if (typeof value !== "object" || value === null) throw Error("not an invocation reference");
  const v: { [key: string]: unknown } = { ...value };
  const { attempt, stage, key, execution, limitMs, elapsedMs, cpu, replay } = v;
  const executions: readonly AttemptRecord["execution"][] = ["executed", "replayed", "timeout-replayed", "timed-out",
    "failed", "interrupted"];
  const foundStage = stageNames.find((s) => s === stage);
  const foundExecution = executions.find((e) => e === execution);
  const c: { [key: string]: unknown } = typeof cpu === "object" && cpu !== null ? { ...cpu } : {};
  // A record written before peak memory was measured has none.
  const peak = c["peakBytes"];
  const readCpu: Cpu | null = typeof c["unavailable"] === "string" ? { unavailable: c["unavailable"] }
    : typeof c["userMs"] === "number" && typeof c["systemMs"] === "number" && typeof c["covers"] === "string" &&
        (peak === undefined || peak === null || typeof peak === "number")
      ? { userMs: c["userMs"], systemMs: c["systemMs"], peakBytes: peak ?? null, covers: c["covers"] } : null;
  if (typeof attempt !== "string" || !foundStage || !(key === null || typeof key === "string") || !foundExecution ||
      !(limitMs === null || typeof limitMs === "number") || typeof elapsedMs !== "number" || !readCpu)
    throw Error(`not an invocation reference: ${JSON.stringify(value).slice(0, 200)}`);
  let readReplay: InvocationReference["replay"] = null;
  if (replay !== null) {
    const r: { [key: string]: unknown } = typeof replay === "object" && replay !== null ? { ...replay } : {};
    const { storedAttempt, storedLimitMs, storedElapsedMs, lookupMs, validationMs, materializationMs } = r;
    if (!(storedLimitMs === null || typeof storedLimitMs === "number") ||
        typeof storedAttempt !== "string" || typeof storedElapsedMs !== "number" || typeof lookupMs !== "number" ||
        typeof validationMs !== "number" || typeof materializationMs !== "number")
      throw Error("not a replay reference");
    readReplay = { storedAttempt, storedLimitMs, storedElapsedMs, lookupMs, validationMs, materializationMs };
  }
  return { attempt, stage: foundStage, key, execution: foundExecution, limitMs, elapsedMs, cpu: readCpu,
    replay: readReplay };
}
const scopes: readonly UnitScope[] = ["census", "module", "outside"];
function readUnit(value: unknown): Unit {
  if (typeof value !== "object" || value === null) throw Error("not a statement unit");
  const v: { [key: string]: unknown } = { ...value };
  const { file, fn, inner, scope, kind, start, end, line, column } = v;
  const foundScope = scopes.find((s) => s === scope);
  if (typeof file !== "string" || typeof fn !== "string" || !(inner === null || typeof inner === "string") ||
      !foundScope || typeof kind !== "string" || typeof start !== "number" || typeof end !== "number" ||
      typeof line !== "number" || typeof column !== "number")
    throw Error(`not a statement unit: ${JSON.stringify(value).slice(0, 200)}`);
  return { file, fn, inner, scope: foundScope, kind, start, end, line, column };
}
function readFileHash(value: unknown): { file: string; sourceSha256: string } {
  if (typeof value !== "object" || value === null) throw Error("not a file hash");
  const v: { [key: string]: unknown } = { ...value };
  const { file, sourceSha256 } = v;
  if (typeof file !== "string" || typeof sourceSha256 !== "string")
    throw Error(`not a file hash: ${JSON.stringify(value).slice(0, 200)}`);
  return { file, sourceSha256 };
}

/** One census as one or more records (the shards of one census) give it:
 * its source, its slices by `file#fn`, and its inventory where the records
 * hold one, each unit once. */
type Census = {
  source: CensusRecord["source"];
  slices: Map<string, SliceRecord>;
  inventory: { files: Map<string, string>; units: Unit[] } | null;
};
function readCensus(paths: string): Census {
  const slices = new Map<string, SliceRecord>();
  let source: Census["source"] | null = null;
  let inventory: Census["inventory"] = null;
  let withoutInventory = 0;
  const names = (x: unknown): string[] | null =>
    Array.isArray(x) && x.every((n) => typeof n === "string") ? x : null;
  for (const path of paths.split(",")) {
    const parsed: unknown = JSON.parse(readFileSync(path, "utf8"));
    if (typeof parsed !== "object" || parsed === null) throw Error(`${path} is no census record`);
    const v: { [key: string]: unknown } = { ...parsed };
    const list = v["slices"];
    if (!Array.isArray(list)) throw Error(`${path} is no census record`);
    for (const s of list.map(readSliceRecord)) slices.set(`${s.file}#${s.fn}`, s);
    const recorded = v["source"];
    const s: { [key: string]: unknown } = typeof recorded === "object" && recorded !== null ? { ...recorded } : {};
    const { commit, dirty, directory, files, functions } = s;
    if (typeof commit !== "string" || typeof dirty !== "boolean" || typeof directory !== "string")
      throw Error(`${path}: no census source`);
    if (source && (source.commit !== commit || source.directory !== directory))
      throw Error(`${path} is a census of ${directory} at ${commit}, the others of ${source.directory} at ${source.commit}`);
    source = { commit, dirty, directory, files: names(files), functions: names(functions) };
    const held = v["inventory"];
    const inv: { [key: string]: unknown } = typeof held === "object" && held !== null ? { ...held } : {};
    const [unitList, fileList] = [inv["units"], inv["files"]];
    if (!Array.isArray(unitList) || !Array.isArray(fileList)) {
      withoutInventory++;
      continue;
    }
    inventory ??= { files: new Map(), units: [] };
    for (const f of fileList.map(readFileHash)) inventory.files.set(f.file, f.sourceSha256);
    const seen = new Set(inventory.units.map((u) => `${u.file}:${u.start}:${u.end}`));
    for (const u of unitList.map(readUnit))
      if (!seen.has(`${u.file}:${u.start}:${u.end}`)) inventory.units.push(u);
  }
  if (!source) throw Error("no census record");
  if (inventory && withoutInventory) throw Error(`${withoutInventory} of the records hold no inventory`);
  return { source, slices, inventory };
}

/** Each slice's outcome by `file#fn`. */
function bySlice(rows: Iterable<SliceRecord>): Map<string, SliceRecord> {
  return new Map([...rows].map((s): [string, SliceRecord] => [`${s.file}#${s.fn}`, s]));
}

/** The inventory of a census's files read from `sources` (the checkout or
 * the census's commit), and how those sources compare with the record's
 * hashes: per file where the record holds file hashes, else per slice. The
 * commit's files are parsed from a copy under the temporary directory: the
 * compiler reads a module another one imports from the disk, so a file is
 * parsed where the disk holds its text. */
function inventoryFromSources(census: Census, sources: "checkout" | "commit"): { units: Unit[]; note: string } {
  const { directory, commit } = census.source;
  const base = sources === "commit"
    ? join(tmpdir(), "tscert-census", sha256(repository).slice(0, 12), `sources-${commit.slice(0, 12)}`, directory)
    : join(repository, directory);
  const read = (file: string): string => sources === "commit"
    ? execFileSync("git", ["-C", repository, "show", `${commit}:${directory}/${file}`], { encoding: "utf8" })
    : readFileSync(join(base, file), "utf8");
  const listed = sources === "commit"
    ? execFileSync("git", ["-C", repository, "ls-tree", "--name-only", `${commit}:${directory}`], { encoding: "utf8" })
      .split("\n")
    : readdirSync(join(repository, directory));
  const files = listed.filter((f) => f.endsWith(".mts") && !f.startsWith("slice-") &&
    (!census.source.files || census.source.files.includes(f))).sort();
  const units: Unit[] = [];
  const differing: string[] = [];
  let compared = 0;
  const texts = files.map((file): [string, string] => [file, read(file)]);
  if (sources === "commit") {
    mkdirSync(base, { recursive: true });
    for (const [file, text] of texts) writeStable(join(base, file), text);
  }
  for (const [file, text] of texts) {
    const tree = openText(join(base, file), text);
    units.push(...inventory(file, tree));
    if (census.inventory) {
      compared++;
      if (census.inventory.files.get(file) !== sha256(text)) differing.push(file);
      continue;
    }
    for (const s of slicesOf(file, tree, text)) {
      const r = census.slices.get(`${s.file}#${s.fn}`);
      if (!r) continue;
      compared++;
      if (r.sourceSha256 !== sha256(s.text)) differing.push(`${s.file}#${s.fn}`);
    }
  }
  closeParser();
  const from = sources === "commit" ? `the census's commit ${commit.slice(0, 12)}` : "the current checkout";
  const what = census.inventory ? "files" : "slices";
  const note = `inventory from ${from}${sources === "commit" && census.source.dirty ? " (the census ran on a dirty tree)" : ""}; ` +
    (differing.length === 0 ? `all ${compared} ${what} match the record's source hashes`
      : `${differing.length} of ${compared} ${what} differ from the record's: ${differing.slice(0, 12).join(", ")}` +
        `${differing.length > 12 ? ", …" : ""}`);
  return { units, note };
}

/** Where an inventory is read for a census without one: its commit, or the
 * checkout for a census of a dirty tree. */
const defaultSources = (census: Census): "checkout" | "commit" => (census.source.dirty ? "checkout" : "commit");

/** The classified inventory of a census: its records', or else one read
 * from its sources. */
function classifiedInventory(census: Census): { units: UnitRecord[]; note: string | null } {
  const found = census.inventory ? { units: census.inventory.units, note: null }
    : inventoryFromSources(census, defaultSources(census));
  return { units: found.units.map((u) => ({ ...u, class: classify(u, census.slices) })), note: found.note };
}

const isTimeout = (s: SliceRecord): boolean => s.detail.startsWith("timeout:");

/** Compare two censuses: gains and losses of verified slices, timeouts,
 * outcome changes, and each stage's cost: CPU time, elapsed time and peak memory. */
function report(before: Map<string, SliceRecord>, after: Map<string, SliceRecord>): void {
  const verified = (m: Map<string, SliceRecord>): Set<string> =>
    new Set([...m].filter(([, s]) => s.status === "verified").map(([k]) => k));
  const [a, b] = [verified(before), verified(after)];
  process.stdout.write(`verified: ${a.size} of ${before.size} → ${b.size} of ${after.size}\n`);
  process.stdout.write(`gained (${[...b].filter((k) => !a.has(k)).length}): ${[...b].filter((k) => !a.has(k)).join(", ")}\n`);
  process.stdout.write(`lost (${[...a].filter((k) => !b.has(k)).length}): ${[...a].filter((k) => !b.has(k)).join(", ")}\n`);
  const timeouts = (m: Map<string, SliceRecord>): string[] => [...m].filter(([, s]) => isTimeout(s)).map(([k]) => k);
  const newTimeouts = timeouts(after).filter((k) => {
    const old = before.get(k);
    return !old || !isTimeout(old);
  });
  process.stdout.write(`timeouts: ${timeouts(before).length} → ${timeouts(after).length}; new: ${newTimeouts.join(", ")}\n`);
  const changed = [...after].filter(([k, s]) => {
    const old = before.get(k);
    return old && (old.status !== s.status || old.phase !== s.phase || blocker(old.detail) !== blocker(s.detail));
  });
  process.stdout.write(`outcomes changed (${changed.length}):\n`);
  for (const [k, s] of changed) {
    const old = before.get(k);
    if (old) process.stdout.write(`  ${k}: ${old.status}/${old.phase} ${blocker(old.detail)} → ${s.status}/${s.phase} ${blocker(s.detail)}\n`);
  }
  const stageCosts = (m: Map<string, SliceRecord>): Map<string, { n: number; cpu: Spread; elapsed: Spread; peak: Spread }> => {
    const costs = new Map<string, Cost[]>();
    for (const s of m.values()) for (const r of s.invocations) costs.set(r.stage, [...(costs.get(r.stage) ?? []), cost(r)]);
    return new Map([...costs].map(([stage, list]) => [stage, { n: list.length, cpu: spread(list.map((c) => c.cpuMs)),
      elapsed: spread(list.map((c) => c.elapsedMs)), peak: spread(list.map((c) => c.peakBytes)) }]));
  };
  const [ta, tb] = [stageCosts(before), stageCosts(after)];
  process.stdout.write("stage cost (each result's producing execution; count, CPU s, elapsed s, peak max MB): " +
    "before → after\n");
  const row = (x: { n: number; cpu: Spread; elapsed: Spread; peak: Spread } | undefined): string => x
    ? `${String(x.n).padStart(5)} ${seconds(x.cpu, "total").padStart(10)} ${seconds(x.elapsed, "total").padStart(8)} ` +
      `${megabytes(x.peak, "max").padStart(5)}`
    : `${"0".padStart(5)} ${"".padStart(10)} ${"".padStart(8)} ${"".padStart(5)}`;
  for (const k of [...new Set([...ta.keys(), ...tb.keys()])].sort())
    process.stdout.write(`  ${k.padEnd(12)} ${row(ta.get(k))} → ${row(tb.get(k))}\n`);
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const args = process.argv.slice(2);
  try {
    if (args[0] === "report" || args[0] === "coverage") {
      const perFunction = args.includes("--per-function");
      const rest = args.slice(1).filter((a) => a !== "--per-function");
      const sources = option(rest, "--sources");
      if (sources !== null && sources !== "checkout" && sources !== "commit")
        throw Error(`--sources takes checkout or commit: ${sources}`);
      const [first, second] = rest;
      if (args[0] === "coverage" && first !== undefined && rest.length === 1) {
        const c = readCensus(first);
        const found = inventoryFromSources(c, sources ?? defaultSources(c));
        process.stdout.write(`${found.note}\n`);
        process.stdout.write(coverageReport(c.source.directory,
          found.units.map((u) => ({ ...u, class: classify(u, c.slices) })), c.slices, perFunction));
      } else if (args[0] === "report" && sources === null && first !== undefined && rest.length === 1) {
        const c = readCensus(first);
        const found = classifiedInventory(c);
        if (found.note) process.stdout.write(`${found.note}\n`);
        process.stdout.write(costReport(c.slices.values()));
        process.stdout.write(coverageReport(c.source.directory, found.units, c.slices, perFunction));
      } else if (args[0] === "report" && sources === null && first !== undefined && second !== undefined &&
          rest.length === 2) {
        const [before, after] = [readCensus(first), readCensus(second)];
        report(before.slices, after.slices);
        const [a, b] = [classifiedInventory(before), classifiedInventory(after)];
        if (a.note) process.stdout.write(`before: ${a.note}\n`);
        if (b.note) process.stdout.write(`after: ${b.note}\n`);
        process.stdout.write(coverageComparison(a.units, b.units));
      } else
        throw Error("usage: node dev/census.mts report <before.json[,…]> <after.json[,…]>\n" +
          "       node dev/census.mts report <record.json[,…]> [--per-function]\n" +
          "       node dev/census.mts coverage <record.json[,…]> [--per-function] [--sources checkout|commit]");
    } else await census(args);
  } catch (error) {
    process.stderr.write(`${basename(import.meta.filename)}: ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 2;
  }
}
