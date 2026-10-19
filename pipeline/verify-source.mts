import { fork, spawnSync, type ChildProcess } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { Socket } from "node:net";
import { availableParallelism } from "node:os";
import { basename, resolve, join } from "node:path";
import { createHash } from "node:crypto";
// ../tools/fragment-parse.mts is the trusted parser and syntactic gate: without it no source becomes the Fragment the producer and Lean read.
import { close as closeParser, parseFile } from "../tools/fragment-parse.mts";
import { clientErrors, tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
import { fieldOf, messageOf } from "../tools/thrown.mts";
import { keepRunDirectories, runDirectory, runRoot } from "./run-directory.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
// ../tools/source-flow.mts checks the shared execution graph wire before proposal.
import { decodeFlowDocument } from "../tools/source-flow.mts";
import { requireWellFormed, wireText } from "../tools/wire-strings.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";

/** A Fragment document this pipeline's parser wrote, read back by a test that
 * forges it. The tests (18 reads) edit fields deep in the document through
 * its type; checking those fields at each test, in place of this assertion,
 * would rewrite each of them, and no TypeScript decoder of the Fragment
 * exists. The assertion stands for the parser's output; it is not checked
 * before the test reads it. */
export function readFragmentFile(file: string): Ast {
  const parsed: unknown = JSON.parse(wireText(readFileSync(file), file));
  requireWellFormed(parsed, file);
  return parsed as Ast; // asserted: the parser wrote the file from an Ast; a check of every field the tests read would cost more than it guards a test's forgery
}

/** A claims document this pipeline's producer wrote, read back by a test that
 * forges it. The tests (83 reads) edit fields deep in the document through
 * its type, and no TypeScript decoder of the claims exists; the assertion
 * stands for the producer's output, unchecked before the test reads it. */
export function readClaimsFile(file: string): SourceClaims {
  const parsed: unknown = JSON.parse(wireText(readFileSync(file), file));
  requireWellFormed(parsed, file);
  return parsed as SourceClaims; // asserted: the producer wrote the file against SourceClaims; a check of every field the tests read would cost more than it guards a test's forgery
}

const here = import.meta.dirname;
// The producer runs from `_build/default/producer.exe` below `../ocaml-producer`.
// Its dune file, `../ocaml-producer/dune`, declares that executable and the library it links;
// `../ocaml-producer/dune-project` makes that directory the root `dune build --root` builds into `_build/`.
export const producerExecutable: string = resolve(here, "../ocaml-producer/_build/default/producer.exe");
const repo = resolve(here, "..");
export const verifier: string =
  process.env.VERIFIER ??
  resolve(repo, "lean/.lake/build/bin/verifier");
function refusalStatus(detail: string): "exhausted" | "unverified" {
  const diagnostic = readDiagnostic(detail);
  if (!diagnostic) return "unverified";
  switch (diagnostic.outcome.kind) {
    case "exhausted": return "exhausted";
    case "not-established": return "unverified";
  }
}
export type Phase = "source" | "proposal" | "search" | "check";
export type Outcome =
  | {
      status: "verified";
      artifacts: string;
      functions: string[];
      /** The source spans of the module initialization's top-level
       * statements, which Lean checked as one unit; empty when the module
       * has no initialization code. */
      initialization: [number, number][];
      phase: "check";
    }
  | {
      status: "unsupported" | "unverified" | "exhausted" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
    };
/** The fuel proof search is given. */
const searchDepth = 12;
/** Wall-clock limit on each external step (the parser, the producer, the
 * search, the check). A step that exceeds it is killed and the case is an
 * error naming the step and the limit, never a verdict. */
const stepTimeoutMs = 60_000;
/** A step run: its exit code, its output, and what it reports on failure. */
type Ran = { code: number; out: string; detail: string };
function run(command: string, args: string[]): Ran {
  const p = spawnSync(command, args, {
    cwd: repo,
    timeout: stepTimeoutMs,
    maxBuffer: 16 * 1024 * 1024,
  });
  const step = [
    basename(command),
    ...args.filter((a) => a.startsWith("--")),
  ].join(" ");
  if (fieldOf(p.error, "code") === "ETIMEDOUT")
    throw Error(
      `timeout: ${step} did not finish within ${stepTimeoutMs / 1000} s`,
    );
  if (p.error || p.signal || p.status === null)
    throw Error(
      `${step}: ${p.error?.message ?? p.signal ?? "no exit status"}`,
    );
  // Every wire document a step prints is valid UTF-8 (`wireText`).
  const out = wireText(p.stdout, step);
  const err = wireText(p.stderr, step);
  return {
    code: p.status,
    out,
    detail: err.trim() || out.trim(),
  };
}
/** A failed search names the obligation it could not establish and why, in
 * source terms: the presentation's summary (`diagnostic-view.mts`) of the verifier's structured record, as
 * the line `obligation: …` after the verifier's own first line. Display only;
 * a record the decoder refuses adds nothing. */
function namingTheObligation(detail: string, source: string): string {
  const record = readDiagnostic(detail);
  const summary = record && presentObligation(record, source).summary;
  if (!summary) return detail;
  const [first, ...rest] = detail.split("\n");
  return [first, `obligation: ${summary}`, ...rest].join("\n");
}
/** One known cause of failure the producer met (`producer --explain`): a
 * form at a source span, and why no derivation of it is found. */
interface Explanation {
  pos: [number, number];
  reason: string;
}
/** What `JSON.parse` gives: null, a Boolean, a number, a string, a fresh
 * array or a fresh plain object of such values. */
type Json = null | boolean | number | string | readonly Json[] | JsonRecord;
type JsonRecord = { readonly [key: string]: Json };
function isJsonArray(value: Json): value is readonly Json[] {
  return Array.isArray(value);
}
function isJsonRecord(value: Json): value is JsonRecord {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
function readExplanations(text: string): Explanation[] {
  try {
    const parsed: Json = JSON.parse(text);
    if (!isJsonArray(parsed)) return [];
    return parsed.flatMap((e: Json): Explanation[] => {
      if (!isJsonRecord(e)) return [];
      const reason = e["reason"];
      const pos = e["pos"];
      if (typeof reason !== "string" || !isJsonArray(pos) || pos.length !== 2) return [];
      const start = pos[0];
      const end = pos[1];
      return typeof start === "number" && typeof end === "number" ? [{ pos: [start, end], reason }] : [];
    });
  } catch {
    return [];
  }
}
/** A search that found no derivation, or a quantified call it could not show
 * within its bound or resolution qualification, is refused by name where its cause is
 * known, on a first line of its own before the verifier's, which follow
 * unchanged: the producer's explanation of a form at the failed obligation
 * (the innermost whose span meets the obligation's), else, for code
 * TypeScript refuses, where the caller asks for it (`--typescript-errors`: it
 * loads the project again, a second of CPU), the TypeScript error nearest
 * the failed obligation: the pipeline follows TypeScript's types. Display only: the outcome is the same unverified search,
 * which Lean decided on the ordinary proposal. */
function refusedByName(detail: string, explain: () => Explanation[],
    read: () => SeenDiagnostic[]): string {
  if (!detail.includes("evidence search failed") &&
      !detail.includes("does not satisfy the closure's bound") &&
      !detail.includes("resolution certificate does not establish")) return detail;
  const at = /at \[(\d+),(\d+)\)/.exec(detail);
  if (at) {
    const [start, end] = [Number(at[1]), Number(at[2])];
    const meets = explain().filter((e) => e.pos[0] < Math.max(end, start + 1) && start < e.pos[1])
      .sort((a, b) => (a.pos[1] - a.pos[0]) - (b.pos[1] - b.pos[0]));
    if (meets.length) return `reject: ${meets[0].reason}\n${detail}`;
  }
  const errors = read();
  if (!errors.length) return detail;
  const pos = at ? Number(at[1]) : 0;
  const distance = (d: SeenDiagnostic) =>
    pos < d.pos[0] ? d.pos[0] - pos : pos > d.pos[1] ? pos - d.pos[1] : 0;
  const nearest = errors.reduce((a, b) => (distance(b) < distance(a) ? b : a));
  const text = nearest.text.split("\n")[0];
  return `reject: TypeScript refuses this code too (line ${nearest.start.line + 1}, col ${
    nearest.start.character + 1}: ${text}); the pipeline follows TypeScript's types\n${detail}`;
}
/** A refusal of the gate or the producer, which names no obligation, is
 * refused by name where TypeScript refuses the code too (`--typescript-errors`):
 * the first TypeScript error of the checked file, on a first line of its own
 * before the refusal, which follows unchanged. The pipeline follows
 * TypeScript's types, and a program TypeScript rejects has none to follow.
 * Display only: the outcome is the same refusal. */
function refusedByTypeScript(detail: string, read: () => SeenDiagnostic[]): string {
  // An import TypeScript does not resolve says where the file was put, not
  // what its code does.
  const errors = read().filter((d) => !d.text.startsWith("Cannot find module"));
  if (!errors.length) return detail;
  const first = errors.reduce((a, b) => (b.pos[0] < a.pos[0] ? b : a));
  return `reject: TypeScript refuses this code too (line ${first.start.line + 1}, col ${
    first.start.character + 1}: ${first.text.split("\n")[0]}); the pipeline follows TypeScript's types\n${detail}`;
}
function typeScriptErrors(file: string, tsconfigPath?: string): SeenDiagnostic[] {
  try {
    return clientErrors(file, tsconfigPath);
  } catch {
    return [];
  }
}
/** The parser run in this process: its Fragment as text, or its refusal,
 * with the TypeScript errors its gate read written to `diagnostics`. */
function parsedHere(diagnostics: string, parse: (seen: (d: SeenDiagnostic) => void) => Ast): Ran {
  const seen: SeenDiagnostic[] = [];
  try {
    return { code: 0, out: JSON.stringify(parse((d) => seen.push(d))), detail: "" };
  } catch (error) {
    return { code: 1, out: "", detail: messageOf(error) };
  } finally {
    writeFileSync(diagnostics, JSON.stringify(seen, null, 1) + "\n");
  }
}
/** A field of a parsed document, `undefined` where it has none. */
const field = (value: unknown, key: string): unknown => fieldOf(value, key);
const list = (value: unknown): unknown[] => (Array.isArray(value) ? value : []);
const spanOf = (value: unknown): [number, number] | null =>
  Array.isArray(value) && value.length === 2 && typeof value[0] === "number" && typeof value[1] === "number"
    ? [value[0], value[1]] : null;
/** A read of an import the pipeline proposes qualified (certified imports):
 * the reading document's name of it, its declaration identity, its module,
 * and its unit's claimed footprint and on-throw flag. */
type QualifiedRead = { local: string; declaration: unknown; module: string; name: string;
  footprint: unknown; onThrow: boolean };
/** A module's claims, kept as text: a bigint literal's digits pass through
 * unrounded. */
type ModuleClaims = { text: string; parsed: unknown };
/** The reads of a document's imported values that may be qualified: a named
 * function import whose declaration is a unit of a module with claims, both
 * readings eligible as Lean requires them (`planImports`), and not
 * withdrawn (`module#name`, or `module#*` for all of a module's). */
function eligibleReads(declarations: unknown, units: Map<string, unknown[]>, claims: Map<string, ModuleClaims>,
    withdrawn: Set<string>): QualifiedRead[] {
  return list(field(declarations, "values")).flatMap((v): QualifiedRead[] => {
    const declaration = field(v, "declaration"), type = field(v, "type"), local = field(field(v, "binding"), "local");
    const module = field(declaration, "module"), name = field(declaration, "name");
    const span = spanOf(field(declaration, "span"));
    if (typeof module !== "string" || typeof name !== "string" || typeof local !== "string" || !span) return [];
    if (withdrawn.has(`${module}#${name}`) || withdrawn.has(`${module}#*`)) return [];
    if (field(v, "construct") !== false || list(field(v, "typeParams")).length > 0 || field(type, "k") !== "function" ||
        field(type, "rest") !== null || field(type, "receiver") !== null ||
        field(field(type, "effect"), "promise") !== null) return [];
    const unit = (units.get(module) ?? []).find((f) => {
      const at = spanOf(field(f, "namePos"));
      return field(f, "name") === name && !!at && span[0] <= at[0] && at[1] <= span[1];
    });
    if (!unit || list(field(unit, "typeParams")).length > 0 || field(unit, "guard") !== null ||
        list(field(unit, "params")).some((p) => field(p, "rest") !== undefined || field(p, "name") === "this")) return [];
    const at = spanOf(field(unit, "namePos"));
    const claimed = list(field(claims.get(module)?.parsed, "functions")).find((f) => {
      const p = spanOf(field(f, "namePos"));
      return field(f, "name") === name && !!p && !!at && p[0] === at[0] && p[1] === at[1];
    });
    const onThrow = field(claimed, "onThrow");
    if (!claimed || typeof onThrow !== "boolean") return [];
    return [{ local, declaration, module, name, footprint: field(claimed, "footprint"), onThrow }];
  });
}
/** Propose a document's claims, its eligible reads qualified. */
function propose(ast: string, flow: string, reads: QualifiedRead[], qualifiedPath: string): Ran {
  writeFileSync(qualifiedPath, JSON.stringify(reads.map(({ local, declaration, footprint, onThrow }) =>
    ({ local, declaration, footprint, onThrow }))));
  return run(producerExecutable, reads.length ? [ast, flow, qualifiedPath] : [ast, flow]);
}
/**
 * The modules of the fragment, each a run of its own: its document,
 * standalone, lowered once and proposed as a file is, at its own eligible
 * reads. A module is proposed after the modules it imports from, so a read
 * may name only a module proposed before it: one closing a cycle of imports
 * is read at its ordinary signature. A module whose lowering or proposal
 * fails is left out.
 */
class ModuleRuns {
  private readonly docs = new Map<string, { index: number; ast: string; flow: string; declarations: unknown;
    imports: string[] }>();
  private readonly units = new Map<string, unknown[]>();
  private readonly proposed = new Map<string, ModuleClaims | null>();
  private readonly artifacts: string;
  constructor(artifacts: string, fragment: unknown) {
    this.artifacts = artifacts;
    const locations = list(field(fragment, "modules")).map((m) => field(m, "location"));
    for (const [index, m] of list(field(fragment, "modules")).entries()) {
      const location = field(m, "location");
      if (typeof location !== "string") continue;
      const doc = { file: location, sourceSha256: field(m, "sourceSha256"), declarations: field(m, "declarations"),
        init: field(m, "init"), functions: field(m, "functions"), modules: [] };
      const ast = join(artifacts, `module-${index}.fragment.json`);
      writeFileSync(ast, JSON.stringify(doc));
      const lowered = run(verifier, ["--lower-control-flow", ast]);
      if (lowered.code !== 0) continue;
      const flow = join(artifacts, `module-${index}.flow.json`);
      writeFileSync(flow, JSON.stringify(decodeFlowDocument(JSON.parse(lowered.out))));
      const imports = [...new Set(list(field(doc.declarations, "values")).map((v) => field(field(v, "declaration"), "module"))
        .filter((l): l is string => typeof l === "string" && l !== location && locations.includes(l)))];
      this.docs.set(location, { index, ast, flow, declarations: doc.declarations, imports });
      this.units.set(location, list(field(m, "functions")));
    }
  }
  /** Each module's claims, and the reads of each module's claims, at the
   * reads not withdrawn; then the importer's eligible reads. */
  claims(declarations: unknown, withdrawn: Set<string>): { claims: Map<string, ModuleClaims>;
      readsOf: Map<string, QualifiedRead[]>; reads: QualifiedRead[] } {
    const claims = new Map<string, ModuleClaims>();
    const readsOf = new Map<string, QualifiedRead[]>();
    const visiting = new Set<string>();
    const visit = (location: string): void => {
      const doc = this.docs.get(location);
      if (!doc || visiting.has(location) || readsOf.has(location)) return;
      visiting.add(location);
      for (const l of doc.imports) visit(l);
      visiting.delete(location);
      const reads = eligibleReads(doc.declarations, this.units, claims, withdrawn);
      readsOf.set(location, reads);
      const key = `${location}\n${JSON.stringify(reads)}`;
      if (!this.proposed.has(key)) {
        const proposed = propose(doc.ast, doc.flow, reads, join(this.artifacts, `module-${doc.index}.qualified.json`));
        writeFileSync(join(this.artifacts, `module-${doc.index}.proposal.log`), proposed.detail);
        this.proposed.set(key, proposed.code === 0 ? { text: proposed.out, parsed: JSON.parse(proposed.out) } : null);
      }
      const proposed = this.proposed.get(key);
      if (proposed) claims.set(location, proposed);
    };
    for (const location of this.docs.keys()) visit(location);
    return { claims, readsOf, reads: eligibleReads(declarations, this.units, claims, withdrawn) };
  }
}
/** The modules whose claims `reads` need, through the modules' own reads. */
function readClosure(reads: QualifiedRead[], readsOf: Map<string, QualifiedRead[]>): string[] {
  const seen: string[] = [];
  for (let work = reads.map((r) => r.module), next = work.shift(); next !== undefined; next = work.shift()) {
    if (seen.includes(next)) continue;
    seen.push(next);
    work.push(...(readsOf.get(next) ?? []).map((r) => r.module));
  }
  return seen;
}
/** The first certified import a failed search or check names, as Lean names
 * it: a qualified read (`certified import <module>#<name>: …`), or a module
 * run (`module <module>: …`). */
function failedImport(detail: string): { module: string; name: string | null } | null {
  const read = /certified import (\S+)#([^:\s]+): /.exec(detail);
  if (read?.[1] && read[2]) return { module: read[1], name: read[2] };
  const run = /module (\S+): /.exec(detail);
  return run?.[1] ? { module: run[1], name: null } : null;
}

/** Acceptance is deliberately private to this module. A proposal alone cannot
 * construct the public verified outcome: both Lean phases must succeed. */
export function check(source: string, tsconfigPath?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number): Outcome {
  const artifacts = runDirectory("pipeline-");
  let phase: Phase = "source";
  try {
    if (subtypeRounds !== undefined && (!Number.isSafeInteger(subtypeRounds) || subtypeRounds < 0))
      throw Error("subtype rounds must be a natural number");
    // Parse a snapshot, not a path whose contents may change during verification.
    const snapshot = join(artifacts, "source.ts");
    const bytes = readFileSync(resolve(source));
    writeFileSync(snapshot, bytes);
    writeFileSync(
      join(artifacts, "tsconfig.json"),
      JSON.stringify({
        compilerOptions: { strict: true, noEmit: true, target: "es2022" },
        files: ["source.ts", resolvableDeclaration],
      }),
    );
    // A caller may name the TypeScript project the source belongs to. The
    // snapshot is parsed, and TypeScript resolves its imports as the original
    // file in that project; the parser requires both to have the same bytes.
    // The producer and verifier still decide whether they can interpret the
    // declarations reached.
    // The TypeScript errors the parser's gate read are kept beside its log,
    // accepted or not: they are where a refusal over one of them points.
    const diagnostics = join(artifacts, "typescript-diagnostics.json");
    const parsed = parsedHere(diagnostics, (seen) =>
      parseFile(snapshot, false, tsconfigPath, tsconfigPath ? resolve(source) : snapshot, seen));
    writeFileSync(join(artifacts, "parse.log"), parsed.detail);
    const refusedErrors = () =>
      typescriptErrors
        ? typeScriptErrors(tsconfigPath ? resolve(source) : snapshot, tsconfigPath)
        : [];
    if (parsed.code !== 0)
      return parsed.detail.startsWith("gate:")
        ? { status: "unsupported", artifacts, phase, detail: refusedByTypeScript(parsed.detail, refusedErrors) }
        : { status: "error", artifacts, phase, detail: parsed.detail };
    const ast = join(artifacts, "fragment.json");
    writeFileSync(ast, parsed.out);
    const parsedData: unknown = JSON.parse(parsed.out);
    if (
      !parsedData ||
      typeof parsedData !== "object" ||
      !("sourceSha256" in parsedData) ||
      parsedData.sourceSha256 !==
        createHash("sha256").update(bytes).digest("hex")
    )
      throw Error("parser fingerprint differs from source snapshot");
    if (!("functions" in parsedData) || !Array.isArray(parsedData.functions))
      throw Error("parser omitted functions");
    const functions = parsedData.functions.map((f: unknown) => {
      if (
        !f ||
        typeof f !== "object" ||
        !("name" in f) ||
        typeof f.name !== "string"
      )
        throw Error("invalid function identity");
      return f.name;
    });
    if (!("init" in parsedData) || !Array.isArray(parsedData.init))
      throw Error("parser omitted the module initialization");
    const initialization = parsedData.init.map((s: unknown): [number, number] => {
      if (!s || typeof s !== "object" || !("pos" in s) || !Array.isArray(s.pos) ||
          s.pos.length !== 2 || !s.pos.every((n: unknown) => typeof n === "number"))
        throw Error("invalid initialization statement position");
      return [s.pos[0], s.pos[1]];
    });
    const flow = join(artifacts, "flow.json");
    const lowered = run(verifier, ["--lower-control-flow", ast]);
    writeFileSync(join(artifacts, "flow.log"), lowered.detail);
    if (lowered.code !== 0)
      return { status: "unsupported", artifacts, phase, detail: lowered.detail };
    writeFileSync(flow, JSON.stringify(decodeFlowDocument(JSON.parse(lowered.out))));
    phase = "proposal";
    // Certified imports: each module's claims, and the reads they may
    // qualify. A read the search or the check refuses, or a module run it
    // refuses, is withdrawn, and the documents proposed again without it.
    const modules = new ModuleRuns(artifacts, parsedData);
    const withdrawn = new Set<string>();
    const claims = join(artifacts, "claims.json"),
      evidence = join(artifacts, "evidence.json");
    const budget = subtypeRounds === undefined ? [] : ["--subtype-rounds", String(subtypeRounds)];
    let produced: Ran;
    for (;;) {
      phase = "proposal";
      const { claims: moduleClaims, readsOf, reads } = modules.claims(field(parsedData, "declarations"), withdrawn);
      const proposed = propose(ast, flow, reads, join(artifacts, "qualified.json"));
      writeFileSync(join(artifacts, "proposal.log"), proposed.detail);
      if (proposed.code !== 0)
        return proposed.detail.startsWith("unsupported:")
          ? { status: "unsupported", artifacts, phase, detail: refusedByTypeScript(proposed.detail, refusedErrors) }
          : { status: "error", artifacts, phase, detail: proposed.detail };
      // The importer's claims, its `modules` the claims of each module a read
      // qualifies, directly or through a module's reads, spliced as text: a
      // bigint literal's digits pass through unrounded.
      const marker = '"modules":[]';
      const at = proposed.out.lastIndexOf(marker);
      if (at < 0) throw Error("the producer's claims state no modules");
      const used = readClosure(reads, readsOf).flatMap((m) => {
        const text = moduleClaims.get(m)?.text;
        return text === undefined ? [] : [text];
      });
      writeFileSync(claims, proposed.out.slice(0, at) + `"modules":[${used.join(",")}]` +
        proposed.out.slice(at + marker.length));
      phase = "search";
      produced = run(verifier, [
        ...budget,
        "--produce-source-claims",
        ast,
        claims,
        snapshot,
        evidence,
        String(searchDepth),
      ]);
      const failed = produced.code !== 0 ? failedImport(produced.detail) : null;
      if (!failed) break;
      const key = `${failed.module}#${failed.name ?? "*"}`;
      if (withdrawn.has(key)) break;
      withdrawn.add(key);
    }
    writeFileSync(join(artifacts, "search.log"), produced.detail);
    if (produced.code !== 0)
      return {
        status: refusalStatus(produced.detail),
        artifacts,
        phase,
        detail: refusedByName(namingTheObligation(produced.detail, bytes.toString("utf8")),
          () => readExplanations(run(producerExecutable, ["--explain", ast, flow]).out),
          refusedErrors),
      };
    phase = "check";
    const checked = run(verifier, [
      ...budget,
      "--check-source-claims",
      ast,
      claims,
      snapshot,
      evidence,
    ]);
    writeFileSync(join(artifacts, "check.log"), checked.detail);
    if (checked.code !== 0)
      return { status: refusalStatus(checked.detail), artifacts, phase, detail: checked.detail };
    return { status: "verified", artifacts, phase, functions, initialization };
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: messageOf(e),
    };
  }
}
const phases: readonly Phase[] = ["source", "proposal", "search", "check"];
const isPhase = (value: unknown): value is Phase => phases.some((p) => p === value);
const isSpan = (value: unknown): value is [number, number] =>
  Array.isArray(value) && value.length === 2 && value.every((n: unknown) => typeof n === "number");
/** The outcome a run in a process of its own printed, read field by field;
 * anything else is refused. */
export function readOutcome(value: unknown): Outcome {
  if (!value || typeof value !== "object" || !("status" in value) || !("artifacts" in value) ||
      !("phase" in value) || typeof value.artifacts !== "string" || !isPhase(value.phase))
    throw Error("not an outcome");
  const { status, artifacts, phase } = value;
  if (status === "verified" && phase === "check" && "functions" in value && Array.isArray(value.functions) &&
      value.functions.every((f: unknown) => typeof f === "string") && "initialization" in value &&
      Array.isArray(value.initialization) && value.initialization.every(isSpan))
    return { status, artifacts, phase, functions: value.functions, initialization: value.initialization };
  if ((status === "unsupported" || status === "unverified" || status === "exhausted" || status === "error") &&
      "detail" in value && typeof value.detail === "string")
    return { status, artifacts, phase, detail: value.detail };
  throw Error("not an outcome");
}
/** What one check is asked: the arguments of `check`, as they cross to a worker. */
type Request = { source: string; project?: string; typescriptErrors: boolean; subtypeRounds?: number };
function readRequest(value: unknown): Request {
  if (!value || typeof value !== "object" || !("source" in value) || typeof value.source !== "string" ||
      !("typescriptErrors" in value) || typeof value.typescriptErrors !== "boolean")
    throw Error("not a request");
  const project = "project" in value && typeof value.project === "string" ? value.project : undefined;
  const subtypeRounds = "subtypeRounds" in value && typeof value.subtypeRounds === "number"
    ? value.subtypeRounds : undefined;
  return { source: value.source, project, typescriptErrors: value.typescriptErrors, subtypeRounds };
}
const checkRequest = (r: Request): Outcome =>
  check(r.source, r.project ? tsconfigOf(r.project) : undefined, r.typescriptErrors, r.subtypeRounds);

/** A whole check is killed after this long: the parser runs inside the worker,
 * so its step has no limit of its own. */
const checkTimeoutMs = 4 * stepTimeoutMs;
type Job = { request: Request; done: (o: Outcome) => void; fail: (e: Error) => void };
const queue: Job[] = [];
const idle: ChildProcess[] = [];
const logs = new Map<ChildProcess, string>();
let workers: number = 0;
/** Give queued checks to idle workers, starting one per core at most. An idle
 * worker does not keep the caller's process alive. */
function dispatch(): void {
  for (let job = queue.shift(); job; job = queue.shift()) {
    const worker = idle.pop() ?? (workers < availableParallelism() ? startWorker() : undefined);
    if (!worker) {
      queue.unshift(job);
      return;
    }
    give(worker, job);
  }
}
function startWorker(): ChildProcess {
  workers++;
  // The workers write their runs under the caller's root, which outlives them.
  runRoot();
  const worker = fork(import.meta.filename, ["--serve"], { cwd: repo, stdio: ["ignore", "ignore", "pipe", "ipc"] });
  // What the worker writes to standard error is shown only with a failure.
  worker.stderr?.setEncoding("utf8");
  worker.stderr?.on("data", (text: unknown) => { logs.set(worker, (logs.get(worker) ?? "") + String(text)); });
  if (worker.stderr instanceof Socket) worker.stderr.unref();
  worker.on("exit", () => {
    workers--;
    const at = idle.indexOf(worker);
    if (at >= 0) idle.splice(at, 1);
    dispatch();
  });
  return worker;
}
function give(worker: ChildProcess, job: Job): void {
  logs.set(worker, "");
  worker.ref();
  worker.channel?.ref();
  const settle = (finish: () => void) => {
    clearTimeout(timer);
    worker.off("message", answered);
    worker.off("exit", died);
    finish();
  };
  const answered = (message: unknown) => settle(() => {
    worker.unref();
    worker.channel?.unref();
    idle.push(worker);
    try {
      job.done(readOutcome(message));
    } catch (error) {
      job.fail(new Error(`no outcome: ${messageOf(error)} ${logs.get(worker)?.trim() ?? ""}`));
    }
    dispatch();
  });
  const died = () => settle(() =>
    job.fail(new Error(`no outcome: the worker for ${job.request.source} exited: ${logs.get(worker)?.trim() ?? ""}`)));
  const timer = setTimeout(() => settle(() => {
    worker.kill();
    job.fail(new Error(`timeout: ${basename(job.request.source)} did not finish within ${checkTimeoutMs / 1000} s`));
  }), checkTimeoutMs);
  worker.on("message", answered);
  worker.on("exit", died);
  worker.send(job.request);
}
/** The same check in one of a pool of worker processes, one per core, each
 * keeping its compiler between checks: for a caller that must stay responsive
 * or runs several at once. `project` is what `--project` takes;
 * `typescriptErrors`, whether a failed search is named by TypeScript's errors
 * (`--typescript-errors`). */
export function checkApart(source: string, project?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number): Promise<Outcome> {
  return new Promise((done, fail) => {
    queue.push({ request: { source, project, typescriptErrors, subtypeRounds }, done, fail });
    dispatch();
  });
}
// A worker of `checkApart`'s pool: one check per message, answered with its outcome.
if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename && process.argv[2] === "--serve") {
  process.on("message", (message: unknown) => {
    let outcome: Outcome;
    try {
      outcome = checkRequest(readRequest(message));
    } catch (error) {
      process.stderr.write(messageOf(error) + "\n");
      process.exit(1);
    }
    process.send?.(outcome);
  });
  process.on("disconnect", () => {
    closeParser();
    process.exit(0);
  });
} else if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const all = process.argv.slice(2);
  const budgetAt = all.indexOf("--subtype-rounds");
  const subtypeRounds = budgetAt < 0 ? undefined : Number(all.splice(budgetAt, 2)[1]);
  const typescriptErrors = all.includes("--typescript-errors");
  const args = all.filter((a) => a !== "--typescript-errors");
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node verify-source.mts file.ts [--project tsconfig-or-directory] [--typescript-errors]" +
      " [--subtype-rounds n]\n");
    process.exitCode = 2;
  } else {
    // The printed outcome names the run's directory, kept for inspection.
    keepRunDirectories();
    try {
      const result = check(args[0], args[2] ? tsconfigOf(args[2]) : undefined, typescriptErrors, subtypeRounds);
      process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write(messageOf(error) + "\n");
      process.exitCode = 1;
    }
  }
}
