// The census of the front end's own functions (WORK.md, "The front end's own
// functions"): each top-level function of a directory's modules sliced into a
// file of its own, with the same-file declarations it uses and the imports
// they name, and each slice run through the pipeline, in the directory's
// copy beside a copy of tools/. Each run writes a census record (DESIGN.md,
// "The stage store"): per slice its source identity, outcome and the
// ordered references to its stage invocations with their timings.
// Processes split the slices with `--shard i/n` and share the stage store.
//   node dev/census.mts [--dir tools] [--files a.mts,…] [--functions f,…] [--shard i/n]
//       [--out dir] [--record file]
//   node dev/census.mts report <before.json[,shard.json…]> <after.json[,shard.json…]>
// The step limit is TSCERT_STEP_LIMIT's, the store TSCERT_STAGE_STORE's.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, relative, resolve } from "node:path";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";
import { checkApart, invocationLog, stepTimeoutMs } from "../pipeline/verify-source.mts";
import { readInvocationLog, storeSetting, type AttemptRecord, type Cpu } from "../pipeline/stages.mts";
import type { StageName } from "../pipeline/stage-execution.mts";
import { runRoot } from "../pipeline/run-directory.mts";

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
};
type CensusRecord = {
  source: { commit: string; dirty: boolean; directory: string; files: string[] | null; functions: string[] | null };
  policy: { store: string; stepLimitMs: number; shard: [number, number] | null };
  started: string;
  elapsedMs: number;
  slices: SliceRecord[];
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
function slicesOf(file: string, path: string, text: string): Slice[] {
  const tree = openText(path, text);
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
  for (const file of readdirSync(join(repository, directory)).filter((f) => f.endsWith(".mts") && !f.startsWith("slice-")).sort()) {
    if (files && !files.includes(file)) continue;
    all.push(...slicesOf(file, join(root, file), readFileSync(join(root, file), "utf8")));
  }
  closeParser();
  const chosen = functions ? all.filter((s) => functions.includes(s.fn)) : all;
  const sliceNames = new Set(chosen.map((s) => s.slice));
  for (const name of readdirSync(root))
    if (name.startsWith("slice-") && name.endsWith(".mts") && !sliceNames.has(name))
      rmSync(join(root, name), { force: true });
  for (const s of chosen) writeStable(join(root, s.slice), s.text);
  const selected = shardPart ? chosen.filter((_, i) => i % shardPart[1] === shardPart[0] - 1) : chosen;
  process.stderr.write(`${selected.length} of ${all.length} slices\n`);

  const project = join(out, "tools");
  let finished = 0;
  const rows = await Promise.all(selected.map(async (s): Promise<SliceRecord> => {
    const path = join(root, s.slice);
    const base = { slice: s.slice, file: s.file, fn: s.fn, lines: s.text.split("\n").length,
      sourceSha256: createHash("sha256").update(s.text).digest("hex") };
    try {
      const o = await checkApart(path, project);
      return { ...base, status: o.status, phase: o.phase, detail: o.status === "verified" ? "" : o.detail.split("\n")[0],
        functions: o.status === "verified" ? o.functions.length : 0,
        invocations: readInvocationLog(join(o.artifacts, invocationLog)).map(reference) };
    } catch (error) {
      return { ...base, status: "error", phase: "-", detail: String(error).split("\n")[0], functions: 0,
        invocations: invocationsOfRequest(path) };
    } finally {
      finished++;
      if (finished % 10 === 0 || finished === selected.length)
        process.stderr.write(`${finished} of ${selected.length} slices\n`);
    }
  }));
  const setting = storeSetting();
  const record: CensusRecord = {
    source: { commit, dirty, directory, files, functions },
    policy: { store: setting.off ? "off" : setting.directory, stepLimitMs: stepTimeoutMs, shard: shardPart },
    started: new Date(Date.now() - (performance.now() - started)).toISOString(),
    elapsedMs: performance.now() - started,
    slices: rows,
  };
  writeFileSync(recordPath, JSON.stringify(record, null, 1) + "\n");
  summarize(record.slices);
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
// Records read back, and compared

function readSliceRecord(value: unknown): SliceRecord {
  if (typeof value !== "object" || value === null) throw Error("not a slice record");
  const v: { [key: string]: unknown } = { ...value };
  const { slice, file, fn, lines, sourceSha256, status, phase, detail, functions, invocations } = v;
  if (typeof slice !== "string" || typeof file !== "string" || typeof fn !== "string" || typeof lines !== "number" ||
      typeof sourceSha256 !== "string" || typeof status !== "string" || typeof phase !== "string" ||
      typeof detail !== "string" || typeof functions !== "number" || !Array.isArray(invocations))
    throw Error(`not a slice record: ${JSON.stringify(value).slice(0, 200)}`);
  return { slice, file, fn, lines, sourceSha256, status, phase, detail, functions,
    invocations: invocations.map(readReference) };
}
function readReference(value: unknown): InvocationReference {
  if (typeof value !== "object" || value === null) throw Error("not an invocation reference");
  const v: { [key: string]: unknown } = { ...value };
  const { attempt, stage, key, execution, limitMs, elapsedMs, cpu, replay } = v;
  const executions: readonly AttemptRecord["execution"][] = ["executed", "replayed", "timeout-replayed", "timed-out",
    "failed", "interrupted"];
  const stages: readonly StageName[] = ["parse", "lower", "propose", "assemble", "search", "check", "explain",
    "diagnostics"];
  const foundStage = stages.find((s) => s === stage);
  const foundExecution = executions.find((e) => e === execution);
  const c: { [key: string]: unknown } = typeof cpu === "object" && cpu !== null ? { ...cpu } : {};
  const readCpu: Cpu | null = typeof c["unavailable"] === "string" ? { unavailable: c["unavailable"] }
    : typeof c["userMs"] === "number" && typeof c["systemMs"] === "number" && typeof c["covers"] === "string"
      ? { userMs: c["userMs"], systemMs: c["systemMs"], covers: c["covers"] } : null;
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
/** The slices of one or more census records (the shards of one census),
 * by `file#fn`. */
function readSlices(paths: string): Map<string, SliceRecord> {
  const slices = new Map<string, SliceRecord>();
  for (const path of paths.split(",")) {
    const parsed: unknown = JSON.parse(readFileSync(path, "utf8"));
    const list: unknown = typeof parsed === "object" && parsed !== null && "slices" in parsed ? parsed.slices : null;
    if (!Array.isArray(list)) throw Error(`${path} is no census record`);
    for (const s of list.map(readSliceRecord)) slices.set(`${s.file}#${s.fn}`, s);
  }
  return slices;
}

const isTimeout = (s: SliceRecord): boolean => s.detail.startsWith("timeout:");

/** Compare two censuses: gains and losses of verified slices, timeouts,
 * outcome changes, and each stage's time, executed and replayed. */
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
  const stageTimes = (m: Map<string, SliceRecord>): Map<string, { n: number; ms: number }> => {
    const sums = new Map<string, { n: number; ms: number }>();
    for (const s of m.values())
      for (const r of s.invocations) {
        const k = `${r.stage} ${r.execution}`;
        const sum = sums.get(k) ?? { n: 0, ms: 0 };
        sum.n++;
        sum.ms += r.elapsedMs;
        sums.set(k, sum);
      }
    return sums;
  };
  const [ta, tb] = [stageTimes(before), stageTimes(after)];
  process.stdout.write("stage time (count, seconds): before → after\n");
  for (const k of [...new Set([...ta.keys(), ...tb.keys()])].sort()) {
    const x = ta.get(k), y = tb.get(k);
    process.stdout.write(`  ${k.padEnd(28)} ${String(x?.n ?? 0).padStart(5)} ${((x?.ms ?? 0) / 1000).toFixed(1).padStart(8)} → ` +
      `${String(y?.n ?? 0).padStart(5)} ${((y?.ms ?? 0) / 1000).toFixed(1).padStart(8)}\n`);
  }
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const args = process.argv.slice(2);
  try {
    if (args[0] === "report") {
      if (args.length !== 3) throw Error("usage: node dev/census.mts report <before.json[,…]> <after.json[,…]>");
      report(readSlices(args[1]), readSlices(args[2]));
    } else await census(args);
  } catch (error) {
    process.stderr.write(`${basename(import.meta.filename)}: ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 2;
  }
}
