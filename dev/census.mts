// The census of a directory's units (docs/DESIGN.md, "Function coverage and
// release thresholds"): each module of the directory checked whole through
// the pipeline, one front per file, each unit (a function, a group of
// functions that reach each other, the initialization) searched and checked
// on its own. A function the parser, the lowering or the producer refuses,
// with its recursive group, and a refused statement of the initialization
// are omitted and the file checked again (`omitted`). A function is shallow
// verified when its unit is accepted, and deep verified when every unit of
// its dependency closure is, computed from the record alone. Each run writes
// a census record (STAGE-STORE.md, "Census records"): per file its rounds, its
// units' results, its omitted units and the ordered references to its stage
// invocations, the edges the census adds to the units' own dependencies, and
// the directory's statement inventory. A selection of files or functions
// checks their dependency closure too, unless `--shallow` or a shard.
//   node dev/census.mts [--dir tools] [--files a.mts,…] [--functions f,…] [--shallow] [--shard i/n]
//       [--out dir] [--record file]
//   node dev/census.mts report <record.json[,shard.json…]> [--per-function]
//   node dev/census.mts report <before.json[,…]> <after.json[,…]>
//   node dev/census.mts coverage <record.json[,…]> [--per-function] [--sources checkout|commit]
//   node dev/census.mts refusals <record.json[,…]>
// `report` prints the shallow and deep counts, the initializations blocking
// deep status with how many functions each blocks, statement coverage under
// both, and each stage's cost, CPU time first; with two records, their
// movement. `coverage` computes statement coverage for a record from the
// sources of its commit (of the checkout for a census of a dirty tree, or by
// `--sources`). `refusals` prints, as JSON, the units whose own result is a
// refusal grouped by the blocker their first refusal names and the source
// text it refuses, each group weighted by its functions' sizes, the heaviest
// first, and each function blocked only through its closure with the unit
// blocking it. The step limit is TSCERT_STEP_LIMIT's, the store
// TSCERT_STAGE_STORE's.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, relative, resolve } from "node:path";
import { close as closeParser, initOmission, openText } from "../tools/fragment-parse.mts";
import { syntax as ts, childrenOf, isTypeAlias } from "../tools/syntax.mts";
import { checkApart, RunFailure, invocationLog, memberName, stepTimeoutMs, type UnitResult } from "../pipeline/verify-source.mts";
import { readInvocationLog, startEviction, storeSetting, type AttemptRecord, type Cpu }
  from "../pipeline/stages.mts";
import { stageNames, type StageName } from "../pipeline/stage-execution.mts";
import { classify, coverageComparison, coverageReport, inventory, type Outcomes, type Unit,
  type UnitScope } from "./statement-coverage.mts";

const repository = resolve(import.meta.dirname, "..");
const sha256 = (text: string): string => createHash("sha256").update(text).digest("hex");

/** A stage invocation, as the census keeps it after its artifacts and the
 * store's entries are gone. */
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

/** Every identifier a node's subtree spells. */
function identifiers(node: ts.Node, into: Set<string>): Set<string> {
  const visit = (n: ts.Node): void => {
    if (ts.isIdentifier(n)) into.add(n.text);
    n.forEachChild(visit);
  };
  visit(node);
  return into;
}

// ---------------------------------------------------------------------------
// A census file's model: its statements, recursive groups and imports

/** A top-level statement of a census file, for locating a refusal: a
 * function by its name, a statement of the initialization with the names its
 * code mentions and whether it is a constant bound to functions only, an
 * import with the names it binds, or another declaration. */
type Statement = { start: number; end: number } &
  ({ kind: "function"; name: string } | { kind: "init"; mentions: Set<string>; functions: boolean } |
    { kind: "import"; names: string[] } | { kind: "other" });
/** What an import binding names in the census directory: a file and an
 * export, `*` for a namespace, or null where it binds outside the directory. */
type ImportTarget = { file: string; imported: string } | null;
/** A census file read for its units: its statements, its functions' recursive
 * groups by the names their code mentions, its imports, and the modules of
 * the directory it loads. */
type SourceModel = {
  file: string;
  text: string;
  statements: Statement[];
  functions: Map<string, { mentions: Set<string>; group: string[] }>;
  initMentions: Set<string>;
  hasInit: boolean;
  imports: Map<string, ImportTarget>;
  loads: string[];
  reexports: { name: string; target: ImportTarget }[];
  /** The names its declarations that run nothing bind: types, interfaces, `const` and ambient enums. */
  types: Set<string>;
  /** The values its initialization binds: constants, cells, classes and enums. */
  values: Set<string>;
  /** The function its `export default function` declares, if any. */
  defaultFunction: string | null;
  lineStarts: number[];
};

/** Whether a top-level statement runs in the module's initialization: a
 * re-export is a module declaration, which runs nothing. */
function runsInInit(s: ts.Statement): boolean {
  const modifiers = childrenOf(s, "modifiers").map((m) => m.kind);
  const declared = modifiers.includes(ts.SyntaxKind.DeclareKeyword);
  return !(isTypeAlias(s) || ts.isInterfaceDeclaration(s) || ts.isFunctionDeclaration(s) || ts.isImportDeclaration(s) ||
    ts.isEmptyStatement(s) || ((ts.isClassDeclaration(s) || ts.isVariableStatement(s)) && declared) ||
    (ts.isEnumDeclaration(s) && (declared || modifiers.includes(ts.SyntaxKind.ConstKeyword))) ||
    (ts.isExportDeclaration(s) && s.moduleSpecifier !== undefined));
}

function sourceModel(root: string, file: string): SourceModel {
  const text = readFileSync(join(root, file), "utf8");
  const tree = openText(join(root, file), text);
  const target = (specifier: ts.Expression | undefined, imported: string): ImportTarget => {
    if (!specifier || !ts.isStringLiteral(specifier) || !specifier.text.startsWith(".")) return null;
    const path = resolve(root, specifier.text);
    return dirname(path) === resolve(root) && existsSync(path) ? { file: basename(path), imported } : null;
  };
  const statements: Statement[] = [];
  const imports = new Map<string, ImportTarget>();
  const loads = new Set<string>();
  const reexports: SourceModel["reexports"] = [];
  const functions = new Map<string, { mentions: Set<string>; group: string[] }>();
  const initMentions = new Set<string>();
  const types = new Set<string>();
  const values = new Set<string>();
  let defaultFunction: string | null = null;
  let hasInit = false;
  for (const s of tree.statements) {
    const span = { start: s.getStart(tree), end: s.end };
    if (ts.isFunctionDeclaration(s) && s.name) {
      statements.push({ ...span, kind: "function", name: s.name.text });
      if (childrenOf(s, "modifiers").some((m) => m.kind === ts.SyntaxKind.DefaultKeyword)) defaultFunction = s.name.text;
      if (s.body) functions.set(s.name.text, { mentions: identifiers(s, new Set()), group: [] });
    } else if (ts.isImportDeclaration(s)) {
      const clause = s.importClause;
      const bindings = clause?.namedBindings;
      const pair = (local: string, imported: string): [string, string] => [local, imported];
      // A type-only import reads no value.
      const typeOnly = clause?.phaseModifier === ts.SyntaxKind.TypeKeyword;
      const names: [string, string][] = typeOnly ? [] : [...(clause?.name ? [pair(clause.name.text, "default")] : []),
        ...(!bindings ? [] : ts.isNamedImports(bindings)
          ? bindings.elements.filter((e) => !e.isTypeOnly).map((e) => pair(e.name.text, (e.propertyName ?? e.name).text))
          : [pair(bindings.name.text, "*")])];
      for (const [local, imported] of names) imports.set(local, target(s.moduleSpecifier, imported));
      const loaded = target(s.moduleSpecifier, "*");
      if (loaded) loads.add(loaded.file);
      statements.push({ ...span, kind: "import", names: names.map(([n]) => n) });
    } else if (ts.isExportDeclaration(s) && s.moduleSpecifier) {
      const loaded = target(s.moduleSpecifier, "*");
      if (loaded) loads.add(loaded.file);
      const clause = s.exportClause;
      if (!clause) reexports.push({ name: "*", target: loaded });
      else if (ts.isNamedExports(clause))
        for (const e of clause.elements)
          reexports.push({ name: e.name.text, target: target(s.moduleSpecifier, (e.propertyName ?? e.name).text) });
      else reexports.push({ name: clause.name.text, target: loaded });
      // A module declaration, no step: its module loads before this one runs.
      statements.push({ ...span, kind: "other" });
    } else if ((isTypeAlias(s) || ts.isInterfaceDeclaration(s) || ts.isEnumDeclaration(s)) && !runsInInit(s)) {
      types.add(s.name.text);
      statements.push({ ...span, kind: "other" });
    } else if (runsInInit(s)) {
      hasInit = true;
      const mentions = identifiers(s, new Set());
      for (const m of mentions) initMentions.add(m);
      if (ts.isVariableStatement(s))
        for (const d of s.declarationList.declarations) for (const n of identifiers(d.name, new Set())) values.add(n);
      if ((ts.isClassDeclaration(s) || ts.isEnumDeclaration(s)) && s.name) values.add(s.name.text);
      statements.push({ ...span, kind: "init", mentions, functions: functionConstant(s) });
    } else statements.push({ ...span, kind: "other" });
  }
  // Recursive groups: functions that reach each other by the names their code mentions.
  const reach = new Map<string, Set<string>>();
  for (const name of functions.keys()) {
    const seen = new Set<string>();
    for (let work = [name], next = work.pop(); next !== undefined; next = work.pop())
      for (const m of functions.get(next)?.mentions ?? [])
        if (functions.has(m) && !seen.has(m)) {
          seen.add(m);
          work.push(m);
        }
    reach.set(name, seen);
  }
  for (const [name, f] of functions)
    f.group = [...functions.keys()].filter((g) => g === name || (reach.get(name)?.has(g) && reach.get(g)?.has(name)));
  const lineStarts = [0];
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") lineStarts.push(i + 1);
  return { file, text, statements, functions, initMentions, hasInit, imports, loads: [...loads], reexports, types,
    values, defaultFunction, lineStarts };
}

/** Whether a statement is a constant whose every initializer is a function
 * expression, through parentheses: it runs nothing, and the parser reads an
 * omitted one at its functions' signatures. */
function functionConstant(s: ts.Statement): boolean {
  const functionValue = (e: ts.Expression | undefined): boolean =>
    !!e && (ts.isParenthesizedExpression(e) ? functionValue(e.expression) : ts.isArrowFunction(e) || ts.isFunctionExpression(e));
  return ts.isVariableStatement(s) && !!(s.declarationList.flags & ts.NodeFlags.Const) &&
    s.declarationList.declarations.every((d) => ts.isIdentifier(d.name) && functionValue(d.initializer));
}

/** The omission a unit's refusal located in a constant of the initialization
 * bound to functions makes: that statement, a function of its own. */
function functionOmission(m: SourceModel, detail: string): string | null {
  const span = /at \[(\d+),(\d+)\)/.exec(detail);
  if (!span) return null;
  const at = Number(span[1]);
  const s = m.statements.find((x) => x.start <= at && at < x.end);
  return s && s.kind === "init" && s.functions ? `${initOmission}@${s.start}` : null;
}

/** The omissions a refusal located in a census file makes: the function
 * whose code holds it, with its recursive group; the statement of the
 * initialization holding it; for an import, every function, with its
 * recursive group, and every statement of the initialization mentioning its
 * bindings. Empty where the refusal names no place, or one no unit owns. */
function omissionsFor(m: SourceModel, detail: string): string[] {
  const span = /at \[(\d+),(\d+)\)/.exec(detail);
  const line = /\(line (\d+), col (\d+)\)/.exec(detail);
  const at = span ? Number(span[1]) : line ? (m.lineStarts[Number(line[1]) - 1] ?? 0) + Number(line[2]) - 1 : null;
  if (at === null) return [];
  const s = m.statements.find((x) => x.start <= at && at < x.end);
  if (!s) return [];
  if (s.kind === "function") return m.functions.get(s.name)?.group ?? [];
  if (s.kind === "init") return [`${initOmission}@${s.start}`];
  if (s.kind === "import")
    return [...new Set([...m.functions].flatMap(([, f]) => s.names.some((n) => f.mentions.has(n)) ? f.group : [])),
      ...m.statements.flatMap((x) => x.kind === "init" && s.names.some((n) => x.mentions.has(n))
        ? [`${initOmission}@${x.start}`] : [])];
  return [];
}

/** A node of the census's dependency closure: a file and a function's name,
 * `initOmission`, or a module run's identity. */
type NodeKey = string;
const nodeKey = (file: string, name: string): NodeKey => `${file}#${name}`;

/** Where an import binding of a census file leads: a function of the
 * directory, the initialization of the module that binds it, or nothing
 * outside the directory or for a type; `unresolved` where a re-export cannot
 * be followed. */
function importNodes(models: (file: string) => SourceModel, t: ImportTarget, depth: number = 0): NodeKey[] | "unresolved" {
  if (t === null) return [];
  const m = models(t.file);
  const init = [nodeKey(m.file, initOmission)];
  if (depth > 8) return "unresolved";
  // A namespace: every function and the initialization, and every re-exported binding.
  if (t.imported === "*") {
    const out = [...[...m.functions.keys()].map((f) => nodeKey(m.file, f)), ...init];
    for (const r of m.reexports) {
      if (r.target === null) continue;
      const nodes = importNodes(models, r.name === "*" ? r.target : r.target, depth + 1);
      if (nodes === "unresolved") return "unresolved";
      out.push(...nodes);
    }
    return out;
  }
  if (t.imported === "default" && !m.reexports.some((r) => r.name === "default"))
    return m.defaultFunction !== null ? [nodeKey(m.file, m.defaultFunction)] : init;
  if (m.functions.has(t.imported)) return [nodeKey(m.file, t.imported)];
  if (m.types.has(t.imported)) return [];
  if (m.values.has(t.imported)) return init;
  const re = m.reexports.find((r) => r.name === t.imported) ?? null;
  if (re) return importNodes(models, re.target, depth + 1);
  // A binding a star re-export may bind, or one the census cannot place.
  return "unresolved";
}

/** The nodes the census adds to a unit's own dependencies: its file's
 * initialization, the same-file functions its code names, the units its code
 * reaches through imports, and, for the
 * initialization, the initialization of every census module it loads. */
function censusEdges(models: (file: string) => SourceModel, m: SourceModel, name: string): NodeKey[] | "unresolved" {
  const out = new Set<NodeKey>();
  if (name !== initOmission) out.add(nodeKey(m.file, initOmission));
  const mentions = name === initOmission ? m.initMentions
    : new Set((m.functions.get(name)?.group ?? []).flatMap((g) => [...(m.functions.get(g)?.mentions ?? [])]));
  // The same-file functions its code names, an omitted one included, which the check reads at its signature.
  for (const f of m.functions.keys()) if (mentions.has(f)) out.add(nodeKey(m.file, f));
  for (const [local, t] of m.imports)
    if (mentions.has(local)) {
      const nodes = importNodes(models, t);
      if (nodes === "unresolved") return "unresolved";
      for (const n of nodes) out.add(n);
    }
  if (name === initOmission) for (const l of m.loads) out.add(nodeKey(l, initOmission));
  out.delete(nodeKey(m.file, name));
  return [...out];
}

// ---------------------------------------------------------------------------
// The census record

/** A unit's own result, as a census record keeps it. */
type OwnResult = { status: string; phase: string; detail: string };
/** A census file as its checks give it: the rounds that omitted units, each
 * with the refusal that did; every omission of its last check with its
 * refusal; the front's refusal of every unit left, or the units' results;
 * the stage invocations of every round; and, per function and for the
 * initialization (`initOmission`), its recursive group and the nodes the
 * census adds to its unit's own dependencies. */
/** A file's progress line: its functions, each verified, rejected (its unit
 * checked and refused) or omitted (refused before its unit's check), and its
 * initialization, accepted or rejected, with the statements left out of it. */
function progress(run: FileRun, omitted: Map<string, OwnResult>): string {
  if (run.front) return `refused: ${run.front.detail.slice(0, 100)}`;
  const functions = (ok: boolean): number => run.units.filter((u) => (u.status === "verified") === ok)
    .reduce((n, u) => n + u.members.filter((m) => m !== "init").length, 0);
  const verified = functions(true), rejected = functions(false);
  const statements = [...omitted.keys()].filter((k) => k.startsWith(`${initOmission}@`)).length;
  const omittedFunctions = omitted.size - statements;
  const init = run.units.find((u) => u.members.includes("init"));
  return `${verified} of ${verified + rejected + omittedFunctions} functions verified` +
    (rejected ? `, ${rejected} rejected` : "") + (omittedFunctions ? `, ${omittedFunctions} omitted` : "") +
    (init ? `; initialization ${init.status === "verified" ? "accepted" : "rejected"}` : "") +
    (statements ? `, ${statements} statement${statements === 1 ? "" : "s"} left out` : "");
}
type FileRun = {
  file: string;
  sourceSha256: string;
  rounds: { omitted: string[]; refusal: OwnResult }[];
  omitted: { name: string; refusal: OwnResult }[];
  front: OwnResult | null;
  units: UnitResult[];
  invocations: InvocationReference[];
  /** Whether the module's initialization runs any statement: one that runs
   * none is accepted with nothing to check. */
  initCode: boolean;
  model: { name: string; group: string[]; edges: NodeKey[] | "unresolved" }[];
};
type CensusRecord = {
  source: { commit: string; dirty: boolean; directory: string; files: string[] | null; functions: string[] | null };
  policy: { store: string; stepLimitMs: number; shard: [number, number] | null };
  started: string;
  elapsedMs: number;
  files: FileRun[];
  /** The statements of the census's files, and each file's source hash. */
  inventory: { files: { file: string; sourceSha256: string }[]; units: Unit[] };
};

/** A unit's own result in a census: an omission's refusal, the front's, or
 * its check's; null where no run of the record covers it. */
function ownResult(runs: ReadonlyMap<string, FileRun>, file: string, name: string):
    { unit: string; own: OwnResult; depends: NodeKey[] } | null {
  const run = runs.get(file);
  if (!run) return null;
  const omitted = run.omitted.find((o) => o.name === name || (name === initOmission && o.name.startsWith(`${initOmission}@`)));
  if (omitted) return { unit: name, own: omitted.refusal, depends: [] };
  if (run.front) return { unit: name, own: run.front, depends: [] };
  const u = run.units.find((x) => x.unit === name || x.members.some((mem) => memberName(mem) === name));
  if (!u && name === initOmission && !run.initCode)
    return { unit: name, own: { status: "verified", phase: "-", detail: "" }, depends: [] };
  if (!u) return null;
  const toNode = (d: string): NodeKey => nodeKey(file, d.startsWith("module:") ? d : memberName(d));
  return { unit: u.unit, own: { status: u.status, phase: u.phase, detail: u.detail }, depends: u.depends.map(toNode) };
}

/** A node's dependencies: its unit's own, accepted, and the census's edges. */
function nodeDepends(runs: ReadonlyMap<string, FileRun>, key: NodeKey): NodeKey[] | "unresolved" {
  const at = key.indexOf("#");
  const file = key.slice(0, at), name = key.slice(at + 1);
  const own = ownResult(runs, file, name);
  if (name.startsWith("module:")) return own?.depends ?? [];
  // The census's edges of every member of the unit the check certified the node with.
  const run = runs.get(file);
  const unit = run?.units.find((u) => u.unit === own?.unit);
  const members = unit ? unit.members.map(memberName) : [name];
  const out = new Set<NodeKey>(own?.depends ?? []);
  for (const member of members) {
    const edges = run?.model.find((x) => x.name === member)?.edges ?? [];
    if (edges === "unresolved") return "unresolved";
    for (const e of edges) out.add(e);
  }
  out.delete(key);
  return [...out];
}

/** The first node of a node's closure, breadth-first, whose unit is not
 * accepted, with its result: what blocks its deep status; null where every
 * unit of the closure is accepted. */
function deepBlocker(runs: ReadonlyMap<string, FileRun>, start: NodeKey): { node: NodeKey; reason: string } | null {
  const seen = new Set<NodeKey>([start]);
  for (let queue = [start], next = queue.shift(); next !== undefined; next = queue.shift()) {
    const at = next.indexOf("#");
    const own = ownResult(runs, next.slice(0, at), next.slice(at + 1));
    if (!own) return { node: next, reason: "not run" };
    if (own.own.status !== "verified") return { node: next, reason: `${own.own.status}/${own.own.phase}: ${own.own.detail}` };
    const deps = nodeDepends(runs, next);
    if (deps === "unresolved") return { node: next, reason: "an import the census cannot resolve" };
    for (const d of deps) if (!seen.has(d)) {
      seen.add(d);
      queue.push(d);
    }
  }
  return null;
}

/** Each census function of a census's files: its own result and its deep
 * status, with what blocks it. */
type FunctionRow = { file: string; fn: string; own: OwnResult | null; blocker: { node: NodeKey; reason: string } | null };
function functionRows(census: Census): FunctionRow[] {
  const rows: FunctionRow[] = [];
  for (const run of census.runs.values())
    for (const { name } of run.model) {
      if (name === initOmission || (census.source.functions && !census.source.functions.includes(name))) continue;
      const own = ownResult(census.runs, run.file, name);
      rows.push({ file: run.file, fn: name, own: own?.own ?? null, blocker: deepBlocker(census.runs, nodeKey(run.file, name)) });
    }
  return rows.sort((a, b) => a.file.localeCompare(b.file) || a.fn.localeCompare(b.fn));
}
const shallow = (r: FunctionRow): boolean => r.own?.status === "verified";
const deep = (r: FunctionRow): boolean => r.blocker === null;

/** The outcome classifying a function's statements, or the initialization's,
 * under shallow or deep status. */
function outcomes(census: Census, rows: readonly FunctionRow[], mode: "shallow" | "deep"): Outcomes {
  const byFunction = new Map(rows.map((r) => [`${r.file}#${r.fn}`, r]));
  return (file, owner) => {
    if (owner !== initOmission) {
      const r = byFunction.get(`${file}#${owner}`);
      if (!r || !r.own) return null;
      if (mode === "shallow" || !shallow(r)) return r.own;
      return r.blocker ? { status: "blocked", phase: "deep", detail: r.blocker.reason } : r.own;
    }
    const own = ownResult(census.runs, file, initOmission)?.own ?? null;
    if (!own || mode === "shallow" || own.status !== "verified") return own;
    const blocker = deepBlocker(census.runs, nodeKey(file, initOmission));
    return blocker ? { status: "blocked", phase: "deep", detail: blocker.reason } : own;
  };
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
 * this checkout, so module paths, and the stage keys embedding them,
 * repeat. */
export function prepare(out: string, directory: string): void {
  const copy = (from: string, to: string, select: (name: string) => boolean): void => {
    mkdirSync(to, { recursive: true });
    const names = new Set(readdirSync(from).filter(select).sort());
    for (const name of readdirSync(to).filter(select))
      if (!names.has(name)) rmSync(join(to, name), { force: true });
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

/** A file checked by units, round by round: a refusal located in a unit
 * omits it, and the file is checked again. */
async function runFile(root: string, project: string, models: (file: string) => SourceModel, m: SourceModel,
    select: string[], omitted: Map<string, OwnResult>): Promise<FileRun> {
  const rounds: FileRun["rounds"] = [];
  const invocations: InvocationReference[] = [];
  const model = [...m.functions.keys(), initOmission].map((name) =>
    ({ name, group: name === initOmission ? [name] : m.functions.get(name)?.group ?? [name],
      edges: censusEdges(models, m, name) }));
  const done = (front: OwnResult | null, units: UnitResult[]): FileRun =>
    ({ file: m.file, sourceSha256: sha256(m.text), rounds, front, units, invocations, model, initCode: m.hasInit,
      omitted: [...omitted].map(([name, refusal]) => ({ name, refusal })) });
  for (;;) {
    let outcome: OwnResult & { units: UnitResult[] | null };
    try {
      using o = await checkApart(join(root, m.file), project, false, undefined, true,
        { omitted: [...omitted.keys()], select });
      invocations.push(...readInvocationLog(join(o.artifacts, invocationLog)).map(reference));
      outcome = { status: o.status, phase: o.phase, detail: o.status === "verified" ? "" : o.detail.split("\n")[0] ?? "",
        units: o.units ?? null };
    } catch (error) {
      if (error instanceof RunFailure) invocations.push(...error.invocations.map(reference));
      outcome = { status: "error", phase: "-", detail: String(error).split("\n")[0] ?? "", units: null };
    }
    if (outcome.units !== null) {
      // A unit refused inside a constant bound to functions: that constant is
      // omitted as a function would be, and the file checked again.
      const located = new Map<string, OwnResult>();
      for (const u of outcome.units) {
        const n = u.status === "verified" ? null : functionOmission(m, u.detail);
        if (n !== null && !omitted.has(n) && !located.has(n))
          located.set(n, { status: u.status, phase: u.phase, detail: u.detail.split("\n")[0] ?? "" });
      }
      if (located.size === 0) return done(null, outcome.units);
      for (const [n, refusal] of located) {
        omitted.set(n, refusal);
        rounds.push({ omitted: [n], refusal });
      }
      continue;
    }
    const refusal = { status: outcome.status, phase: outcome.phase, detail: outcome.detail };
    // A file whose every unit is omitted has nothing left to check.
    if (outcome.detail.includes("no functions in file")) return done(null, []);
    const next = outcome.status === "error" ? [] : omissionsFor(m, outcome.detail).filter((n) => !omitted.has(n));
    if (next.length === 0) return done(refusal, []);
    for (const n of next) omitted.set(n, refusal);
    rounds.push({ omitted: next, refusal });
  }
}

async function census(args: string[]): Promise<void> {
  startEviction();
  const directory = option(args, "--dir") ?? "tools";
  const files = option(args, "--files")?.split(",") ?? null;
  const functions = option(args, "--functions")?.split(",") ?? null;
  const shardText = option(args, "--shard");
  const shard = shardText === null ? null : /^(\d+)\/(\d+)$/.exec(shardText);
  if (shardText !== null && (!shard || Number(shard[1]) < 1 || Number(shard[1]) > Number(shard[2])))
    throw Error(`--shard takes i/n with 1 ≤ i ≤ n: ${shardText}`);
  const shardPart: [number, number] | null = shard ? [Number(shard[1]), Number(shard[2])] : null;
  const shallowOnly = args.includes("--shallow") || shardPart !== null;
  const out = resolve(option(args, "--out") ?? join(tmpdir(), "tscert-census", sha256(repository).slice(0, 12), directory));
  const commit = execFileSync("git", ["-C", repository, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
  const dirty = execFileSync("git", ["-C", repository, "status", "--porcelain", "--", "tools", directory, "pipeline"],
    { encoding: "utf8" }).trim() !== "";
  const recordPath = resolve(option(args, "--record") ??
    join(out, "..", `census-${directory}-${commit.slice(0, 12)}-${new Date().toISOString().replace(/[:.]/g, "-")}${
      shardPart ? `-${shardPart[0]}-of-${shardPart[1]}` : ""}.json`));
  const rest = args.filter((a) => a !== "--shallow");
  if (rest.length) throw Error(`unknown arguments: ${rest.join(" ")}`);
  const started = performance.now();
  prepare(out, directory);
  const root = join(out, directory);
  const project = join(out, "tools");
  const cache = new Map<string, SourceModel>();
  const models = (file: string): SourceModel => {
    const known = cache.get(file);
    if (known) return known;
    const m = sourceModel(root, file);
    cache.set(file, m);
    return m;
  };
  const all = readdirSync(root).filter((f) => f.endsWith(".mts")).sort();
  const chosen = all.filter((f, i) => (!files || files.includes(f)) && (!shardPart || i % shardPart[1] === shardPart[0] - 1));
  const want = new Map<string, Set<string>>();
  const add = (file: string, name: string): boolean => {
    const set = want.get(file) ?? new Set<string>();
    want.set(file, set);
    if (set.has(name)) return false;
    set.add(name);
    return true;
  };
  for (const file of chosen) {
    const m = models(file);
    for (const fn of m.functions.keys()) if (!functions || functions.includes(fn)) add(file, fn);
    if (!functions && m.hasInit) add(file, initOmission);
  }
  const runs = new Map<string, FileRun>();
  const omissions = new Map<string, Map<string, OwnResult>>();
  const ran = new Map<string, string>();
  // The statement inventory, read once; the record, written after each round, so a stopped census keeps its rounds.
  const units: Unit[] = [];
  const fileHashes: { file: string; sourceSha256: string }[] = [];
  for (const file of chosen) {
    const text = readFileSync(join(root, file), "utf8");
    units.push(...inventory(file, openText(join(root, file), text)));
    fileHashes.push({ file, sourceSha256: sha256(text) });
  }
  closeParser();
  const setting = storeSetting();
  const writeRecord = (): void => {
    const record: CensusRecord = {
      source: { commit, dirty, directory, files, functions },
      policy: { store: setting.off ? "off" : setting.directory, stepLimitMs: stepTimeoutMs, shard: shardPart },
      started: new Date(Date.now() - (performance.now() - started)).toISOString(),
      elapsedMs: performance.now() - started,
      files: [...runs.values()],
      inventory: { files: fileHashes, units },
    };
    writeFileSync(recordPath, JSON.stringify(record, null, 1) + "\n");
  };
  for (let round = 1; ; round++) {
    // A file whose initialization runs nothing has nothing to check for it.
    const checked = (file: string, names: Set<string>): string[] =>
      [...names].filter((n) => n !== initOmission || models(file).hasInit).sort();
    const due = [...want].filter(([file, names]) => checked(file, names).length > 0 &&
      ran.get(file) !== checked(file, names).join(","));
    // A module whose initialization runs nothing, wanted for its initialization alone, is recorded unchecked.
    for (const [file, names] of want)
      if (!runs.has(file) && checked(file, names).length === 0) {
        const m = models(file);
        runs.set(file, { file, sourceSha256: sha256(m.text), rounds: [], omitted: [], front: null, units: [], invocations: [],
          initCode: false, model: [initOmission].map((name) => ({ name, group: [name], edges: censusEdges(models, m, name) })) });
      }
    if (due.length === 0) break;
    process.stderr.write(`round ${round}: ${due.length} files, ${due.reduce((n, [, s]) => n + s.size, 0)} units wanted\n`);
    let finished = 0;
    await Promise.all(due.map(async ([file, names]) => {
      const select = checked(file, names);
      ran.set(file, select.join(","));
      const known = omissions.get(file) ?? new Map<string, OwnResult>();
      omissions.set(file, known);
      const run = await runFile(root, project, models, models(file), select, known);
      runs.set(file, run);
      process.stderr.write(`  [${++finished}/${due.length}] ${file}: ${progress(run, known)}\n`);
    }));
    writeRecord();
    if (shallowOnly) break;
    for (const [file, names] of [...want])
      for (const name of [...names]) {
        const deps = nodeDepends(runs, nodeKey(file, name));
        if (deps === "unresolved") continue;
        for (const d of deps) {
          const at = d.indexOf("#");
          if (!d.slice(at + 1).startsWith("module:")) add(d.slice(0, at), d.slice(at + 1));
        }
      }
  }
  writeRecord();
  process.stdout.write(summary(readCensus(recordPath), false));
  process.stdout.write(`record: ${recordPath}\n`);
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

/** Each stage's cost over a census's invocations, each stage result counted
 * once: CPU, then elapsed, then peak memory; and the files that cost the most
 * CPU. */
function costReport(runs: Iterable<FileRun>, top: number = 10): string {
  const files = [...runs];
  const seen = new Set<string>();
  const distinct = (r: InvocationReference): boolean => {
    const k = r.key === null ? r.attempt : `${r.stage}:${r.key}`;
    if (seen.has(k)) return false;
    seen.add(k);
    return true;
  };
  const byFile = files.map((f) => ({ f, invocations: f.invocations.filter(distinct) }));
  const byStage = new Map<StageName, InvocationReference[]>();
  for (const { invocations } of byFile) for (const r of invocations) byStage.set(r.stage, [...(byStage.get(r.stage) ?? []), r]);
  const lines = ["stage cost (each result's producing execution, each result once; seconds, peak MB):",
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
  const perFile = byFile.map(({ f, invocations }) => {
    const costs = invocations.map(cost);
    return { f, cpu: spread(costs.map((x) => x.cpuMs)), elapsed: spread(costs.map((x) => x.elapsedMs)),
      peak: spread(costs.map((x) => x.peakBytes)) };
  });
  lines.push(`files by CPU (top ${Math.min(top, perFile.length)}; seconds, peak MB):`);
  for (const { f, cpu, elapsed, peak } of perFile.sort((a, b) => b.cpu.total - a.cpu.total).slice(0, top))
    lines.push(`  ${seconds(cpu, "total").padStart(10)} CPU ${seconds(elapsed, "total").padStart(8)} elapsed ` +
      `${megabytes(peak, "max").padStart(5)} MB  ${f.file}: ${f.front ? `refused ${f.front.status}/${f.front.phase}`
        : `${f.units.filter((u) => u.status === "verified").length} of ${f.units.length} units accepted`}`);
  return lines.join("\n") + "\n";
}

// ---------------------------------------------------------------------------
// Records read back

/** A JSON value's own field. */
const field = (value: unknown, key: string): unknown =>
  typeof value === "object" && value !== null && Object.hasOwn(value, key)
    ? Object.getOwnPropertyDescriptor(value, key)?.value : undefined;
const strings = (value: unknown, what: string): string[] => {
  if (!Array.isArray(value) || !value.every((x): x is string => typeof x === "string")) throw Error(`${what} is no list of strings`);
  return value;
};
function readOwn(value: unknown): OwnResult {
  const status = field(value, "status"), phase = field(value, "phase"), detail = field(value, "detail");
  if (typeof status !== "string" || typeof phase !== "string" || typeof detail !== "string")
    throw Error(`not a unit's result: ${String(JSON.stringify(value)).slice(0, 200)}`);
  return { status, phase, detail };
}
const unitStatuses: readonly UnitResult["status"][] = ["verified", "unverified", "exhausted", "error"];
function readUnitResult(value: unknown): UnitResult {
  const unit = field(value, "unit"), phase = field(value, "phase"), detail = field(value, "detail");
  const status = unitStatuses.find((s) => s === field(value, "status"));
  if (typeof unit !== "string" || !status || (phase !== "search" && phase !== "check") || typeof detail !== "string")
    throw Error(`not a unit result: ${String(JSON.stringify(value)).slice(0, 200)}`);
  return { unit, members: strings(field(value, "members"), "a unit's members"), status, phase, detail,
    depends: strings(field(value, "depends"), "a unit's dependencies") };
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
  const peak = c["peakBytes"];
  const readCpu: Cpu | null = typeof c["unavailable"] === "string" ? { unavailable: c["unavailable"] }
    : typeof c["userMs"] === "number" && typeof c["systemMs"] === "number" && typeof c["covers"] === "string" &&
        (peak === null || typeof peak === "number")
      ? { userMs: c["userMs"], systemMs: c["systemMs"], peakBytes: peak, covers: c["covers"] } : null;
  if (typeof attempt !== "string" || !foundStage || !(key === null || typeof key === "string") || !foundExecution ||
      !(limitMs === null || typeof limitMs === "number") || typeof elapsedMs !== "number" || !readCpu)
    throw Error(`not an invocation reference: ${String(JSON.stringify(value)).slice(0, 200)}`);
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
function readFileRun(value: unknown): FileRun {
  const file = field(value, "file"), sourceSha256 = field(value, "sourceSha256"), front = field(value, "front");
  const list = (key: string): unknown[] => {
    const x = field(value, key);
    if (!Array.isArray(x)) throw Error(`a file run's ${key} is no list`);
    return x;
  };
  const initCode = field(value, "initCode");
  if (typeof file !== "string" || typeof sourceSha256 !== "string" || typeof initCode !== "boolean")
    throw Error(`not a file run: ${String(JSON.stringify(value)).slice(0, 200)}`);
  return {
    file, sourceSha256, initCode,
    rounds: list("rounds").map((r) => ({ omitted: strings(field(r, "omitted"), "a round's omissions"),
      refusal: readOwn(field(r, "refusal")) })),
    omitted: list("omitted").map((o) => {
      const name = field(o, "name");
      if (typeof name !== "string") throw Error("an omission without its name");
      return { name, refusal: readOwn(field(o, "refusal")) };
    }),
    front: front === null ? null : readOwn(front),
    units: list("units").map(readUnitResult),
    invocations: list("invocations").map(readReference),
    model: list("model").map((x) => {
      const name = field(x, "name"), edges = field(x, "edges");
      if (typeof name !== "string") throw Error("a unit's model without its name");
      return { name, group: strings(field(x, "group"), "a unit's group"),
        edges: edges === "unresolved" ? "unresolved" : strings(edges, "a unit's edges") };
    }),
  };
}
const scopes: readonly UnitScope[] = ["census", "module", "outside"];
function readUnit(value: unknown): Unit {
  const file = field(value, "file"), fn = field(value, "fn"), inner = field(value, "inner"), kind = field(value, "kind");
  const scope = scopes.find((s) => s === field(value, "scope"));
  const [start, end, line, column] = ["start", "end", "line", "column"].map((k) => field(value, k));
  if (typeof file !== "string" || typeof fn !== "string" || !(inner === null || typeof inner === "string") || !scope ||
      typeof kind !== "string" || typeof start !== "number" || typeof end !== "number" || typeof line !== "number" ||
      typeof column !== "number")
    throw Error(`not a statement unit: ${String(JSON.stringify(value)).slice(0, 200)}`);
  return { file, fn, inner, scope, kind, start, end, line, column };
}

/** One census as one or more records (the shards of one census) give it:
 * its source, its files' runs, its statement inventory, and its elapsed time. */
type Census = {
  source: CensusRecord["source"];
  runs: Map<string, FileRun>;
  inventory: { files: Map<string, string>; units: Unit[] };
  elapsedMs: number;
};
function readCensus(paths: string): Census {
  let source: Census["source"] | null = null;
  const runs = new Map<string, FileRun>();
  const inventory: Census["inventory"] = { files: new Map(), units: [] };
  let elapsedMs = 0;
  for (const path of paths.split(",")) {
    const parsed: unknown = JSON.parse(readFileSync(path, "utf8"));
    const s = field(parsed, "source"), inv = field(parsed, "inventory"), elapsed = field(parsed, "elapsedMs");
    const commit = field(s, "commit"), dirty = field(s, "dirty"), directory = field(s, "directory");
    const files = field(s, "files"), functions = field(s, "functions");
    const runList = field(parsed, "files"), fileList = field(inv, "files"), unitList = field(inv, "units");
    if (typeof commit !== "string" || typeof dirty !== "boolean" || typeof directory !== "string" ||
        typeof elapsed !== "number" || !Array.isArray(runList) || !Array.isArray(fileList) || !Array.isArray(unitList))
      throw Error(`${path} is no census record`);
    if (source && (source.commit !== commit || source.directory !== directory))
      throw Error(`${path} is a census of ${directory} at ${commit}, the others of ${source.directory} at ${source.commit}`);
    source = { commit, dirty, directory, files: files === null ? null : strings(files, "the census's files"),
      functions: functions === null ? null : strings(functions, "the census's functions") };
    elapsedMs = Math.max(elapsedMs, elapsed);
    for (const r of runList.map(readFileRun)) runs.set(r.file, r);
    for (const f of fileList) {
      const file = field(f, "file"), hash = field(f, "sourceSha256");
      if (typeof file !== "string" || typeof hash !== "string") throw Error(`${path}: a file hash is malformed`);
      inventory.files.set(file, hash);
    }
    const seen = new Set(inventory.units.map((u) => `${u.file}:${u.start}:${u.end}`));
    for (const u of unitList.map(readUnit))
      if (!seen.has(`${u.file}:${u.start}:${u.end}`)) inventory.units.push(u);
  }
  if (!source) throw Error("no census record");
  return { source, runs, inventory, elapsedMs };
}

// ---------------------------------------------------------------------------
// Reports

/** A detail without its line, column and span: the blocker it names. */
const blocker = (detail: string): string =>
  detail.replace(/\(line \d+, col \d+\)/, "").replace(/ at \[\d+,\d+\).*/, "").slice(0, 140);

/** The initializations that block deep status, each with its own refusal
 * and how many functions' deep status it blocks first. */
function initializationBlockers(rows: readonly FunctionRow[], runs: ReadonlyMap<string, FileRun>):
    { node: NodeKey; refusal: string; functions: number }[] {
  const counts = new Map<NodeKey, number>();
  for (const r of rows) if (shallow(r) && r.blocker && r.blocker.node.endsWith(`#${initOmission}`))
    counts.set(r.blocker.node, (counts.get(r.blocker.node) ?? 0) + 1);
  return [...counts].map(([node, functions]) => {
    const at = node.indexOf("#");
    const own = ownResult(runs, node.slice(0, at), initOmission)?.own;
    return { node, functions, refusal: own ? `${own.status}/${own.phase}: ${blocker(own.detail)}` : "not run" };
  }).sort((a, b) => b.functions - a.functions);
}

/** A census's shallow and deep counts, the initializations blocking deep
 * status, statement coverage under both, and its cost. */
function summary(c: Census, perFunction: boolean): string {
  const rows = functionRows(c);
  const out: string[] = [];
  const counts: Record<string, number> = {};
  for (const r of rows) {
    const k = r.own ? (r.own.detail.startsWith("timeout:") ? "timeout" : `${r.own.status}/${r.own.phase}`) : "not run";
    counts[k] = (counts[k] ?? 0) + 1;
  }
  out.push(`functions: ${rows.length}; shallow verified ${rows.filter(shallow).length}; own results ${JSON.stringify(counts)}`);
  out.push(`deep status (computed, not a headline figure): ${rows.filter(deep).length} deep verified`);
  const blockers = new Map<string, number>();
  for (const r of rows.filter((x) => !shallow(x) && x.own)) {
    const b = blocker(r.own?.detail ?? "");
    blockers.set(b, (blockers.get(b) ?? 0) + 1);
  }
  for (const [b, n] of [...blockers].sort((a, b) => b[1] - a[1])) out.push(`${String(n).padStart(4)} ${b}`);
  out.push("initializations blocking deep status (functions blocked first by each):");
  for (const b of initializationBlockers(rows, c.runs)) out.push(`  ${String(b.functions).padStart(4)}  ${b.node}  ${b.refusal}`);
  if (perFunction)
    for (const r of rows)
      out.push(`  ${r.file}#${r.fn}: ${r.own ? `${r.own.status}/${r.own.phase}` : "not run"}${deep(r) ? " deep" : ""}` +
        `${r.own && !shallow(r) ? ` ${blocker(r.own.detail)}` : ""}` +
        `${!deep(r) && shallow(r) && r.blocker ? ` · blocked by ${r.blocker.node} (${blocker(r.blocker.reason)})` : ""}`);
  out.push(costReport(c.runs.values()).trimEnd());
  for (const mode of ["shallow", "deep"] as const) {
    const classified = c.inventory.units.map((u) => ({ ...u, class: classify(u, outcomes(c, rows, mode)) }));
    out.push(`${mode}:`);
    out.push(coverageReport(c.source.directory, classified, rows.map((r) => ({ file: r.file,
      verified: mode === "shallow" ? shallow(r) : deep(r) })), perFunction).trimEnd());
  }
  out.push(`elapsed: ${(c.elapsedMs / 1000).toFixed(0)} s`);
  return out.join("\n") + "\n";
}

/** Compare two censuses: shallow and deep gains and losses, outcome changes,
 * statement coverage and each stage's cost. */
function comparison(before: Census, after: Census): string {
  const [a, b] = [functionRows(before), functionRows(after)];
  const out: string[] = [];
  for (const [name, test] of [["shallow", shallow], ["deep", deep]] as const) {
    const [x, y] = [new Set(a.filter(test).map((r) => `${r.file}#${r.fn}`)), new Set(b.filter(test).map((r) => `${r.file}#${r.fn}`))];
    out.push(`${name} verified: ${x.size} of ${a.length} → ${y.size} of ${b.length}`);
    out.push(`  gained (${[...y].filter((k) => !x.has(k)).length}): ${[...y].filter((k) => !x.has(k)).join(", ")}`);
    out.push(`  lost (${[...x].filter((k) => !y.has(k)).length}): ${[...x].filter((k) => !y.has(k)).join(", ")}`);
  }
  const old = new Map(a.map((r) => [`${r.file}#${r.fn}`, r]));
  const changed = b.filter((r) => {
    const o = old.get(`${r.file}#${r.fn}`);
    return o && (o.own?.status !== r.own?.status || o.own?.phase !== r.own?.phase ||
      blocker(o.own?.detail ?? "") !== blocker(r.own?.detail ?? ""));
  });
  out.push(`own results changed (${changed.length}):`);
  for (const r of changed) {
    const o = old.get(`${r.file}#${r.fn}`);
    out.push(`  ${r.file}#${r.fn}: ${o?.own?.status}/${o?.own?.phase} ${blocker(o?.own?.detail ?? "")} → ` +
      `${r.own?.status}/${r.own?.phase} ${blocker(r.own?.detail ?? "")}`);
  }
  for (const mode of ["shallow", "deep"] as const)
    out.push(`${mode}: ` + coverageComparison(
      before.inventory.units.map((u) => ({ ...u, class: classify(u, outcomes(before, a, mode)) })),
      after.inventory.units.map((u) => ({ ...u, class: classify(u, outcomes(after, b, mode)) }))).trimEnd());
  out.push("before:", costReport(before.runs.values()).trimEnd(), "after:", costReport(after.runs.values()).trimEnd());
  return out.join("\n") + "\n";
}

/** The inventory of a census's files read from `sources` (the checkout or
 * the census's commit), and how those sources compare with the record's
 * hashes. The commit's files are parsed from a copy under the temporary
 * directory: the compiler reads a module another one imports from the disk,
 * so a file is parsed where the disk holds its text. */
function inventoryFromSources(c: Census, sources: "checkout" | "commit"): { units: Unit[]; note: string } {
  const { directory, commit } = c.source;
  const base = sources === "commit"
    ? join(tmpdir(), "tscert-census", sha256(repository).slice(0, 12), `sources-${commit.slice(0, 12)}`, directory)
    : join(repository, directory);
  const read = (file: string): string => sources === "commit"
    ? execFileSync("git", ["-C", repository, "show", `${commit}:${directory}/${file}`], { encoding: "utf8" })
    : readFileSync(join(base, file), "utf8");
  const files = [...c.inventory.files.keys()].sort();
  const texts = files.map((file): [string, string] => [file, read(file)]);
  if (sources === "commit") {
    mkdirSync(base, { recursive: true });
    for (const [file, text] of texts) writeStable(join(base, file), text);
  }
  const units: Unit[] = [];
  const differing: string[] = [];
  for (const [file, text] of texts) {
    units.push(...inventory(file, openText(join(base, file), text)));
    if (c.inventory.files.get(file) !== sha256(text)) differing.push(file);
  }
  closeParser();
  const from = sources === "commit" ? `the census's commit ${commit.slice(0, 12)}` : "the current checkout";
  const note = `inventory from ${from}${sources === "commit" && c.source.dirty ? " (the census ran on a dirty tree)" : ""}; ` +
    (differing.length === 0 ? `all ${files.length} files match the record's source hashes`
      : `${differing.length} of ${files.length} files differ from the record's: ${differing.slice(0, 12).join(", ")}` +
        `${differing.length > 12 ? ", …" : ""}`);
  return { units, note };
}

/** The source text a unit's first refusal names, its span read from the
 * census's copy of the file, when that copy still holds the text the census
 * checked (its hash in the record); null otherwise. */
function refusedText(record: string, directory: string, run: FileRun, detail: string): string | null {
  const span = /at \[(\d+),(\d+)\)/.exec(detail);
  const path = join(dirname(record), directory, directory, run.file);
  if (!span || !existsSync(path)) return null;
  const text = readFileSync(path, "utf8");
  if (sha256(text) !== run.sourceSha256) return null;
  return text.slice(Number(span[1]), Number(span[2])).replace(/\s+/g, " ");
}

/** The functions whose own result is a refusal, grouped by the blocker
 * their first refusal names and the source text it refuses: each group's
 * statements, its function count, its weight and each function's detail,
 * the heaviest first; and each function verified shallow but not deep with
 * the unit blocking it. A function of n statements weighs 10 / (10 + n): one
 * whose first refusal is cleared verifies sooner the fewer statements, and
 * refusals, it holds. */
function refusals(c: Census, record: string): {
  groups: { reason: string; text: string | null; weight: number; statements: number; functions: number; sites: string[] }[];
  deep: { function: string; blocker: string; reason: string }[] } {
  const rows = functionRows(c);
  const statements = new Map<string, number>();
  for (const u of c.inventory.units)
    if (u.scope === "census") statements.set(`${u.file}#${u.fn}`, (statements.get(`${u.file}#${u.fn}`) ?? 0) + 1);
  const groups = new Map<string,
    { reason: string; text: string | null; weight: number; statements: number; functions: number; sites: string[] }>();
  for (const r of rows) {
    if (!r.own || shallow(r)) continue;
    const run = c.runs.get(r.file);
    const reason = blocker(r.own.detail), text = run ? refusedText(record, c.source.directory, run, r.own.detail) : null;
    const key = `${r.file}#${r.fn}`, n = statements.get(key) ?? 0;
    const group = groups.get(`${reason}\n${text}`) ?? { reason, text, weight: 0, statements: 0, functions: 0, sites: [] };
    group.weight += 10 / (10 + n);
    group.statements += n;
    group.functions++;
    group.sites.push(`${key} (${n} statements): ${r.own.detail}`);
    groups.set(`${reason}\n${text}`, group);
  }
  return { groups: [...groups.values()].sort((a, b) => b.weight - a.weight || b.functions - a.functions),
    deep: rows.filter((r) => shallow(r) && r.blocker).map((r) => ({ function: `${r.file}#${r.fn}`,
      blocker: r.blocker?.node ?? "", reason: blocker(r.blocker?.reason ?? "") })) };
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const args = process.argv.slice(2);
  try {
    if (args[0] === "refusals" && args[1] !== undefined && args.length === 2)
      process.stdout.write(JSON.stringify(refusals(readCensus(args[1]), args[1]), null, 1) + "\n");
    else if (args[0] === "report" || args[0] === "coverage") {
      const perFunction = args.includes("--per-function");
      const rest = args.slice(1).filter((a) => a !== "--per-function");
      const sources = option(rest, "--sources");
      if (sources !== null && sources !== "checkout" && sources !== "commit")
        throw Error(`--sources takes checkout or commit: ${sources}`);
      const [first, second] = rest;
      if (args[0] === "coverage" && first !== undefined && rest.length === 1) {
        const c = readCensus(first);
        const found = inventoryFromSources(c, sources ?? (c.source.dirty ? "checkout" : "commit"));
        process.stdout.write(`${found.note}\n`);
        process.stdout.write(summary({ ...c, inventory: { ...c.inventory, units: found.units } }, perFunction));
      } else if (args[0] === "report" && sources === null && first !== undefined && rest.length === 1)
        process.stdout.write(summary(readCensus(first), perFunction));
      else if (args[0] === "report" && sources === null && first !== undefined && second !== undefined && rest.length === 2)
        process.stdout.write(comparison(readCensus(first), readCensus(second)));
      else
        throw Error("usage: node dev/census.mts report <before.json[,…]> <after.json[,…]>\n" +
          "       node dev/census.mts report <record.json[,…]> [--per-function]\n" +
          "       node dev/census.mts coverage <record.json[,…]> [--per-function] [--sources checkout|commit]");
    } else await census(args);
  } catch (error) {
    process.stderr.write(`${basename(import.meta.filename)}: ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 2;
  }
}
