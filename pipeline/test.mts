// The pipeline's suite: every case of the inventory, then the checks no case
// can make.
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { tmpdir } from "node:os";
import { createHash } from "node:crypto";
import { parseFile, close as closeParser } from "../tools/fragment-parse.mts";
import { collectDeclarations, tsconfigOf } from "../tools/declaration-graph.mts";
import { overlay as arrayOverlay } from "../tools/array-prototype.mts";
import type { Ast } from "../tools/fragment.mts";
import type { TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { check, checkApart, producerExecutable, verifier } from "./verify-source.mts";
import { cases } from "./cases.mts";
import { expectOutcome, pooled, runCase } from "./run-cases.mts";
import type { Row, SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
// Forged-claim controls on single cases, each in a file of its own:
// generic-rest.mts, a universal rest claim past collection, substitution and binding;
// rest-pack-instance.mts, a forged non-array instance of a type parameter typing a value and a rest, at a call and at a `new`;
// overload-claims.mts, per-signature claims across the same independent boundary;
// default-parameters.mts, forged claims about parameter defaults: their scope, a generic closure's default, a capture read before its initialization.
import { checkGenericRest } from "./generic-rest.mts";
import { checkRestPackInstance } from "./rest-pack-instance.mts";
import { checkOverloads } from "./overload-claims.mts";
import { checkDefaults, checkSchemeDefaults, checkEarlyDefault, checkPatternDefaults } from "./default-parameters.mts";
import vm from "node:vm";
import { decodeFlowDocument, type ExecutionPlan, type ExecutionOperation } from "../tools/source-flow.mts";
// ../tools/strip-types.mts erases the annotations of an example the suite runs as JavaScript.
import { stripTypes } from "../tools/strip-types.mts";
const here = import.meta.dirname;
const libraryConfig = tsconfigOf(resolve(here, "library-project"));

function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
/** An example run as JavaScript, then `expression` evaluated after it. */
const runExample = (file: string, expression: string): unknown =>
  vm.runInNewContext(`${stripTypes(readFileSync(join(here, "examples", `${file}.ts`), "utf8"))
    .replace(/^export /gm, "")}\n${expression}`, {}, { timeout: 1000 });
/** Run a value-import example as Node runs its ES modules, then print
 * `expression`: the example and the modules of `imports-project` it imports
 * are stripped of types, `@fixture/NAME` resolved to `NAME`'s module. */
const runImporting = (file: string, expression: string): unknown => {
  const out = mkdtempSync(join(tmpdir(), "imports-"));
  const project = join(here, "imports-project");
  const relink = (text: string): string => stripTypes(text).replace(/from "@fixture\/([\w-]+)"/g, 'from "./$1.mjs"');
  for (const name of ["lib", "relay"])
    writeFileSync(join(out, `${name}.mjs`), relink(readFileSync(join(project, `${name}.ts`), "utf8")));
  writeFileSync(join(out, "main.mjs"), `${relink(readFileSync(join(here, "examples", `${file}.ts`), "utf8"))}
console.log(JSON.stringify(${expression}));
`);
  const run = spawnSync(process.execPath, [join(out, "main.mjs")], { encoding: "utf8", timeout: 30_000 });
  assert.ifError(run.error);
  assert.equal(run.status, 0, run.stderr);
  const printed: unknown = JSON.parse(run.stdout);
  return printed;
};
/** Run an example as TypeScript's own emit compiles it, then `expression`:
 * an enum, which type stripping does not erase, and whose member reads a
 * transforming stripper may replace by their values. TypeScript emits the
 * file whatever errors it reports. */
const runEmitted = (file: string, expression: string): unknown => {
  const out = mkdtempSync(join(tmpdir(), "emitted-"));
  const tsc = spawnSync(join(here, "..", "tools", "node_modules", ".bin", "tsc"),
    ["--target", "es2022", "--strict", "--outDir", out, join(here, "examples", `${file}.ts`)], { encoding: "utf8", timeout: 60_000 });
  assert.ifError(tsc.error);
  return vm.runInNewContext(`${readFileSync(join(out, `${file}.js`), "utf8")}\n${expression}`, {}, { timeout: 1000 });
};
/** Check `claims` against `evidence` with the verifier's acceptance entry, and
 * require a refusal; its words, for the caller to match. */
const invoke = (claims: string, evidence: string, artifacts: string,
  ast = join(artifacts, "fragment.json")): string => {
  const p = spawnSync(verifier, ["--check-source-claims", ast, claims, join(artifacts, "source.ts"), evidence],
    { encoding: "utf8", timeout: 30_000 });
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
  return p.stdout + p.stderr;
};
/** Search for evidence of forged claims, or of a forged parser document. */
const produceWith = (artifacts: string, claims: string, name: string,
    fragmentPath = join(artifacts, "fragment.json")): SpawnSyncReturns<string> =>
  spawnSync(verifier, ["--produce-source-claims", fragmentPath, claims, join(artifacts, "source.ts"),
    join(artifacts, `${name}-evidence.json`), "12"], { encoding: "utf8", timeout: 30_000 });
/** Require search over forged claims to fail at the obligation named `at`. */
const refusedAt = (artifacts: string, claims: string, name: string, at: string): void => {
  const searched = produceWith(artifacts, claims, name);
  const detail = searched.stdout + searched.stderr;
  assert.equal(searched.status, 1, detail);
  assert.ok(detail.includes(at), detail);
};
/** The label of the one-clause row `clause`, added to the claims' rows when
 * they lack it. */
const rowOf = (claims: SourceClaims, clause: Row[number]): number => {
  const i = claims.types.findIndex((row) => row.length === 1 && JSON.stringify(row[0]) === JSON.stringify(clause));
  return i >= 0 ? i : claims.types.push([clause]) - 1;
};
const readClaims = (artifacts: string): SourceClaims =>
  JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
/** Write forged claims beside a run's artifacts. */
const writeClaims = (artifacts: string, name: string, claims: SourceClaims): string => {
  const path = join(artifacts, `${name}.json`);
  writeFileSync(path, JSON.stringify(claims));
  return path;
};
/** A TypeScript project of `files`, strict, with `@fixture/NAME` mapped to
 * `NAME.ts`; `graphOf` collects the declaration graph of a client importing
 * from it, `parse` parses such a client. */
function fixtureProject(files: Record<string, string>) {
  const dir = mkdtempSync(join(tmpdir(), "tscert-fixture-project-"));
  for (const [name, text] of Object.entries(files)) writeFileSync(join(dir, name), text);
  const config = join(dir, "tsconfig.json");
  writeFileSync(config, JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, module: "Node16", moduleResolution: "Node16",
      paths: Object.fromEntries(Object.keys(files).filter((f) => f.endsWith(".ts") && !f.endsWith(".d.ts"))
        .map((f) => [`@fixture/${f.replace(/\.ts$/, "")}`, [`./${f}`]])) },
    include: ["*.ts"],
  }));
  let clients = 0;
  const client = (text: string) => {
    const file = join(dir, `client-${clients++}.ts`);
    writeFileSync(file, text);
    return file;
  };
  return {
    graphOf: (text: string) => collectDeclarations(client(text), { tsconfigPath: config }),
    parse: (text: string) => parseFile(client(text), false, config),
  };
}

// ../ocaml-producer/speculation_tests.ml checks the producer's scoped-state contract directly.
{
  const result = spawnSync(resolve(here, "../ocaml-producer/_build/default/speculation_tests.exe"), [],
    { encoding: "utf8", timeout: 30_000 });
  assert.ifError(result.error);
  assert.equal(result.signal, null);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  process.stdout.write(result.stdout);
}

const outcomes = await pooled(cases, runCase);
const artifactsOf = new Map<string, string>();
let verifiedFunctions = 0;
for (const [i, test] of cases.entries()) {
  const settled = outcomes[i];
  if (settled.status === "rejected") throw settled.reason;
  const result = expectOutcome(test, settled.value);
  if (result.status === "verified") verifiedFunctions += result.functions.length;
  else if (test.kind === "negative" && (test.phase === "search" || test.phase === "check"))
    assert.match(result.detail, /at \[\d+,\d+\)|obligation at \d+/, `${test.file}: a control failing at no located obligation`);
  artifactsOf.set(test.file, result.artifacts);
  process.stdout.write(`${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`);
}
process.stdout.write(
  `${verifiedFunctions} functions verified; ${cases.filter((c) => c.kind === "negative").length} negative controls; ${cases.filter((c) => c.kind === "gap").length} named gaps\n`,
);
/** The artifacts of a case's run. */
const run = (file: string): string => must(artifactsOf.get(file), `case ${file}'s run`);

// Candidate alternatives retain substituted-type exhaustion in both CLI modes.
// Reuse the source case's accepted artifact bundle and its selected instance.
{
  const settled = outcomes[cases.findIndex(c => c.file === "generic-callable-bound")];
  assert(settled?.status === "fulfilled");
  const result = settled.value;
  assert.equal(result.status, "verified");
  const at = (name: string) => join(result.artifacts, name);
  const source = readFileSync(at("source.ts"), "utf8");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const evidence = mode === "--produce-source-claims" ? at("budget-evidence.json") : at("evidence.json");
    const runWith = (rounds: number) => spawnSync(verifier,
      ["--subtype-rounds", String(rounds), mode, at("fragment.json"), at("claims.json"),
        at("source.ts"), evidence, ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    const limited = runWith(0);
    assert.ifError(limited.error);
    assert.equal(limited.status, 1, limited.stdout + limited.stderr);
    const diagnostic = readDiagnostic(limited.stderr);
    assert(diagnostic, limited.stderr);
    assert.equal(diagnostic.outcome.kind, "exhausted");
    assert.match(presentObligation(diagnostic, source).searchOutcome, /exhausted.*inconclusive/);
    const sufficient = runWith(8);
    assert.ifError(sufficient.error);
    assert.equal(sufficient.status, 0, sufficient.stdout + sufficient.stderr);
  }
  process.stdout.write("instance alternatives retain substituted-type exhaustion in both CLI modes\n");
}

// A broad, shallow finite comparison has no semantic dependency-count cap.
// Distinct child keys keep each comparison necessary; the changed leaf is
// checked through the same source path as the equivalent pair.
{
  const dir = mkdtempSync(join(tmpdir(), "tscert-wide-subtyping-"));
  const width = 205;
  const names = Array.from({ length: width }, (_, i) => i);
  const source = (bad: boolean) => [
    ...names.flatMap(i => [
      `interface A${i} { readonly p${i}: number }`,
      `interface B${i} { readonly p${i}: ${bad && i === width - 1 ? "string" : "number"} }`,
    ]),
    `interface A { ${names.map(i => `readonly f${i}: A${i}`).join("; ")} }`,
    `interface B { ${names.map(i => `readonly f${i}: B${i}`).join("; ")} }`,
    "export function convert(value: A): B { return value; }",
  ].join("\n");
  const positive = join(dir, "positive.ts");
  const negative = join(dir, "negative.ts");
  writeFileSync(positive, source(false));
  writeFileSync(negative, source(true));
  const wide = check(positive);
  assert.equal(wide.status, "verified", "205 finite readonly dependencies");
  // One submitted derivation crosses both modes under the requested budget.
  // A low budget may refuse it; increasing resources preserves its meaning.
  const wideAst = join(wide.artifacts, "fragment.json");
  const wideClaims = join(wide.artifacts, "claims.json");
  const wideSource = join(wide.artifacts, "source.ts");
  const wideEvidence = join(wide.artifacts, "evidence.json");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const args = [mode, wideAst, wideClaims, wideSource, wideEvidence,
      ...(mode === "--produce-source-claims" ? ["12"] : [])];
    const runWith = (rounds: number) => spawnSync(verifier,
      ["--subtype-rounds", String(rounds), ...args], { encoding: "utf8", timeout: 30_000 });
    const limited = runWith(0);
    assert.equal(limited.status, 1, `${mode}: zero frontier rounds cannot establish the record comparison`);
    if (mode === "--produce-source-claims") {
      const diagnostic = readDiagnostic(limited.stderr);
      assert(diagnostic?.kind === "direct-obligation", limited.stderr);
      assert.equal(diagnostic.judgment.kind, "subtyping");
      assert.deepEqual(diagnostic.sourceMap.context, []);
      assert(diagnostic.sourceMap.pos[0] > 0);
      assert.deepEqual(diagnostic.outcome, {
        kind: "exhausted",
        resource: { kind: "subtype-frontier", limit: 0, rounds: 0, visited: 0 },
      });
      const view = presentObligation(diagnostic, source(false));
      assert.match(view.searchOutcome, /exhausted.*limit 0.*inconclusive/);
    }
    const sufficient = runWith(8);
    assert.equal(sufficient.status, 0, `${mode}: eight frontier rounds establish the finite graph: ${sufficient.stderr}`);
  }
  assert.equal(check(positive, undefined, false, 0).status, "exhausted",
    "the source runner distinguishes exhausted work from a completed refusal");
  assert.equal((await checkApart(positive, undefined, false, 0)).status, "exhausted",
    "the subprocess outcome decoder preserves exhaustion");
  assert.equal(check(negative).status, "unverified", "the last field's type is incompatible");
}
// An instance bound cannot cite the comparison currently being established.
// Forged declarations exercise this boundary independently of source parsing:
// <T>(value: T) => T has a checked instance at Source; changing its bound to
// Target makes validating that instance depend on the unfinished Source ≤ Target.
{
  const source = "type Source = (value: unknown) => never;\n" +
    "type Target = (value: Source) => Source;\n" +
    "export function convert(value: Source): Target { return value; }\n";
  const file = join(mkdtempSync(join(tmpdir(), "tscert-circular-instance-")), "client.ts");
  writeFileSync(file, source);
  const ordinary = check(file);
  assert.equal(ordinary.status, "verified");
  const at = (name: string) => join(ordinary.artifacts, name);
  const fragment: Ast = JSON.parse(readFileSync(at("fragment.json"), "utf8"));
  const definition = fragment.declarations.definitions.find(d => d.declaration.name === "Source");
  const target = fragment.declarations.definitions.find(d => d.declaration.name === "Target");
  assert(definition && target);
  const span = definition.expression.span;
  const parameter: TypeTerm = { k: "binder", name: "T", span };
  const quantified: Extract<TypeTerm, { k: "scheme" }> = {
    k: "scheme", binders: [{ name: "T", bound: { k: "atom", name: "unknown", span }, default: null, resolution: null, span }],
    signatures: [{ k: "function", effect: "unrestricted", receiver: { k: "atom", name: "unknown", span },
      params: [parameter], rest: null, result: parameter, span }], span,
  };
  definition.expression = quantified;
  writeFileSync(at("identity-ast.json"), JSON.stringify(fragment));
  const evidence = at("identity-evidence.json");
  const run = (mode: string, ast: string) => spawnSync(verifier,
    [mode, at(ast), at("claims.json"), at("source.ts"), evidence,
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
    { encoding: "utf8", timeout: 30_000 });
  const produced = run("--produce-source-claims", "identity-ast.json");
  assert.equal(produced.status, 0, produced.stderr);
  const checked = run("--check-source-claims", "identity-ast.json");
  assert.equal(checked.status, 0, checked.stderr);
  function hasInstance(value: unknown): boolean {
    if (value === null || typeof value !== "object") return false;
    if ("instantiation" in value && value.instantiation !== null) return true;
    return Object.values(value).some(hasInstance);
  }
  assert(hasInstance(JSON.parse(readFileSync(evidence, "utf8"))), "the positive evidence uses a checked instance");
  const bound = quantified.binders[0];
  assert(bound);
  bound.bound = { k: "reference", reference: { name: "Target", span, arguments: [], target: target.declaration },
    args: [], span };
  writeFileSync(at("circular-ast.json"), JSON.stringify(fragment));
  // Consumption comes first: production must not overwrite the valid evidence.
  const circularCheck = run("--check-source-claims", "circular-ast.json");
  assert.equal(circularCheck.status, 1);
  assert.match(circularCheck.stdout + circularCheck.stderr, /source evidence does not justify the extracted program and exact claims/);
  const circularSearch = run("--produce-source-claims", "circular-ast.json");
  assert.equal(circularSearch.status, 1);
  const diagnostic = readDiagnostic(circularSearch.stderr);
  assert(diagnostic?.kind === "node-typing", circularSearch.stderr);
  const location = diagnostic.source.sourceMap;
  assert(location);
  assert.equal(location.role, "return-contract");
  assert.equal(source.slice(...location.pos), "value");
  assert.equal(diagnostic.outcome.kind, "not-established");
  process.stdout.write("an instance bound citing its unfinished comparison: refused in both modes\n");
}
// Extra valid coercions exercise exhaustion during consumption, after extraction.
{
  const field = (v: unknown, key: string): unknown =>
    v !== null && typeof v === "object" ? Reflect.get(v, key) : undefined;
  function parameterTypes(v: unknown): unknown[] | undefined {
    const node = field(v, "node"), context = field(field(node, "claim"), "context");
    if (field(node, "rule") === "var" && Array.isArray(context) && context.length === 2) return context;
    if (v !== null && typeof v === "object") for (const child of Object.values(v)) {
      const found = parameterTypes(child);
      if (found) return found;
    }
    return undefined;
  }
  function insertCoercions(v: unknown, types: unknown[]): number {
    const node = field(v, "node"), claim = field(node, "claim"), type = field(claim, "type");
    const current = types.findIndex(t => JSON.stringify(t) === JSON.stringify(type));
    if (current >= 0 && field(node, "rule") === "var" && v !== null && typeof v === "object" &&
        "node" in v && claim !== null && typeof claim === "object") {
      const rule = { sub: { proof: { instantiation: null, members: [] } } };
      const inner = { node: { claim: { ...claim, type: types[1 - current] }, rule, premises: [structuredClone(v)] } };
      v.node = { claim, rule, premises: [inner] };
      return 1;
    }
    return v !== null && typeof v === "object"
      ? Object.values(v).reduce((n: number, child: unknown) => n + insertCoercions(child, types), 0) : 0;
  }
  const declarations = ["interface AChild { readonly n: number }", "interface BChild { readonly n: number }",
    "interface A { readonly x: AChild }", "interface B { readonly x: BChild }"].join("\n");
  for (const site of ["graph", "code", "obligation"]) {
    const source = declarations + "\nexport function keep(value: A, other: B): A {\n" +
      (site === "graph" ? "" : "  const read = (input: A): A => { const old = other; return input; };\n") + "  return value;\n}\n";
    const file = join(mkdtempSync(join(tmpdir(), "tscert-consumer-budget-")), "client.ts");
    writeFileSync(file, source);
    const admitted = check(file);
    assert.equal(admitted.status, "verified");
    const at = (name: string) => join(admitted.artifacts, name);
    const run = (evidence: string, rounds: number) => spawnSync(verifier,
      ["--subtype-rounds", String(rounds), "--check-source-claims", at("fragment.json"), at("claims.json"),
        at("source.ts"), evidence], { encoding: "utf8", timeout: 30_000 });
    assert.equal(run(at("evidence.json"), 0).status, 0, `${site}: original evidence needs no frontier rounds`);
    const evidence: unknown = JSON.parse(readFileSync(at("evidence.json"), "utf8"));
    const types = parameterTypes(evidence);
    assert(types && types.length === 2);
    const functions = field(evidence, "functions");
    assert(Array.isArray(functions) && functions.length === 1);
    const target = site === "graph" ? field(functions[0], "certificate") :
      site === "code" ? field(functions[0], "codes") : field(evidence, "obligations");
    assert(insertCoercions(target, types) > 0, `${site}: a coercion was inserted`);
    const extra = at("extra-coercions.json");
    writeFileSync(extra, JSON.stringify(evidence));
    const stopped = run(extra, 0);
    assert.equal(stopped.status, 1);
    const diagnostic = readDiagnostic(stopped.stderr);
    assert(diagnostic?.kind === "direct-obligation", stopped.stderr);
    assert.equal(diagnostic.phase, "certificate-check");
    assert.equal(diagnostic.judgment.kind, "subtyping");
    assert.equal(diagnostic.outcome.kind, "exhausted");
    assert.deepEqual(diagnostic.sourceMap.context, []);
    assert.deepEqual(diagnostic.judgment.subject, diagnostic.sourceMap.pos);
    const located = source.slice(...diagnostic.sourceMap.pos);
    if (site === "obligation") assert.match(located, /^\(input: A\): A =>/);
    else assert.equal(located, site === "graph" ? "value" : "input");
    assert.match(presentObligation(diagnostic, source).searchOutcome, /exhausted.*inconclusive/);
    const enough = run(extra, 8);
    assert.equal(enough.status, 0, `${site}: added coercions verify with enough resources: ${enough.stderr}`);
  }
}
// Module-call bounds run before a graph request exists. Both CLI modes must
// retain the unfinished comparison at the call, rather than claim a bad bound.
{
  const dir = mkdtempSync(join(tmpdir(), "tscert-bound-budget-"));
  const file = join(dir, "bounded.ts");
  const text = [
    "interface A { readonly x: { readonly n: number } }",
    "interface B { readonly x: { readonly n: number } }",
    "function bounded<T extends B>(value: T): T { return value; }",
    "export function convert(value: A): A { return bounded(value); }",
  ].join("\n");
  writeFileSync(file, text);
  const admitted = check(file, undefined, false, 8);
  assert.equal(admitted.status, "verified", JSON.stringify(admitted));
  const at = text.lastIndexOf("bounded(value)");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const run: SpawnSyncReturns<string> = spawnSync(verifier, ["--subtype-rounds", "0", mode,
      ...["fragment.json", "claims.json", "source.ts", "evidence.json"].map(f => join(admitted.artifacts, f)),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      {encoding: "utf8", timeout: 30_000});
    assert.equal(run.status, 1, run.stderr);
    const diagnostic = readDiagnostic(run.stderr);
    assert(diagnostic?.kind === "direct-obligation", run.stderr);
    assert.equal(diagnostic.phase, "request-validation");
    assert.equal(diagnostic.outcome.kind, "exhausted");
    assert.equal(diagnostic.sourceMap.role, "scheme-elimination");
    assert.deepEqual(diagnostic.sourceMap.pos, [at, at + "bounded(value)".length]);
    assert.equal(diagnostic.judgment.kind, "subtyping");
  }
}
// A source annotation's application bound is checked during equation lowering.
// This path retains the compacted type graph and the application's own span.
{
  const dir = mkdtempSync(join(tmpdir(), "tscert-annotation-budget-"));
  const file = join(dir, "annotation.ts");
  const text = [
    "interface A { readonly n: number }",
    "interface B { readonly n: number }",
    "type Box<T extends B> = { readonly value: T };",
    "export function unbox(value: Box<A>): A { return value.value; }",
  ].join("\n");
  writeFileSync(file, text);
  const admitted = check(file, undefined, false, 8);
  assert.equal(admitted.status, "verified", JSON.stringify(admitted));
  const at = text.indexOf("Box<A>");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const run: SpawnSyncReturns<string> = spawnSync(verifier, ["--subtype-rounds", "0", mode,
      ...["fragment.json", "claims.json", "source.ts", "evidence.json"].map(f => join(admitted.artifacts, f)),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      {encoding: "utf8", timeout: 30_000});
    assert.equal(run.status, 1, run.stderr);
    const diagnostic = readDiagnostic(run.stderr);
    assert(diagnostic?.kind === "direct-obligation", run.stderr);
    assert.equal(diagnostic.phase, "request-validation");
    assert.equal(diagnostic.outcome.kind, "exhausted");
    assert.equal(diagnostic.sourceMap.role, "binding-annotation");
    assert.deepEqual(diagnostic.sourceMap.pos, [at, at + "Box<A>".length]);
    assert.equal(diagnostic.judgment.kind, "subtyping");
    const view = presentObligation(diagnostic, text);
    assert.match(view.searchOutcome, /exhausted.*inconclusive/);
    assert.doesNotMatch(view.summary ?? "", /call's type argument/);
  }
}
// An equivalent parameter claim must be checked, including when consuming
// previously produced evidence. A source-side row scan cannot authorize it.
{
  const dir = mkdtempSync(join(tmpdir(), "tscert-signature-budget-"));
  const file = join(dir, "signature.ts");
  writeFileSync(file, [
    "interface A { readonly n: number }",
    "interface B { readonly n: number }",
    "export function inspect(first: A, second: B): number { return second.n; }",
  ].join("\n"));
  const admitted = check(file);
  assert.equal(admitted.status, "verified", JSON.stringify(admitted));
  const claims: SourceClaims = JSON.parse(readFileSync(join(admitted.artifacts, "claims.json"), "utf8"));
  const fn = claims.functions.find(f => f.name === "inspect");
  assert(fn);
  const first = fn.params[0], second = fn.params[1];
  assert(first && second);
  second.type = structuredClone(first.type);
  const equalClaims = join(dir, "equal-claims.json");
  writeFileSync(equalClaims, JSON.stringify(claims));
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const runWith = (n: number): SpawnSyncReturns<string> => spawnSync(verifier, ["--subtype-rounds", String(n), mode,
      join(admitted.artifacts, "fragment.json"), equalClaims, join(admitted.artifacts, "source.ts"),
      join(admitted.artifacts, "evidence.json"), ...(mode === "--produce-source-claims" ? ["12"] : [])],
      {encoding: "utf8", timeout: 30_000});
    const limited = runWith(0);
    assert.equal(limited.status, 1, limited.stderr);
    const diagnostic = readDiagnostic(limited.stderr);
    assert(diagnostic?.kind === "direct-obligation", limited.stderr);
    assert.equal(diagnostic.outcome.kind, "exhausted");
    assert.equal(diagnostic.sourceMap.role, "entry-claim");
    assert.deepEqual(diagnostic.sourceMap.pos, fn.namePos);
    assert.equal(diagnostic.judgment.kind, "subtyping");
    const sufficient = runWith(8);
    assert.equal(sufficient.status, 0, sufficient.stderr);
  }
}

{
  // Node's declarations the `process` examples read: `@types/node` at the
  // version library-project/package.json pins (`npm ci --prefix pipeline/library-project`).
  // `process` and the members those examples read are declared in these two files.
  const nodeSha = (path: string) =>
    createHash("sha256").update(readFileSync(resolve(here, "library-project/node_modules/@types/node", path))).digest("hex");
  const nodeTypes: unknown = JSON.parse(readFileSync(resolve(here,
    "library-project/node_modules/@types/node/package.json"), "utf8"));
  assert.ok(nodeTypes && typeof nodeTypes === "object" && "version" in nodeTypes &&
    nodeTypes.version === "22.10.7", "run `npm ci --prefix pipeline/library-project`");
  assert.equal(nodeSha("globals.d.ts"),
    "ba97261afafe85aafe76d988e65e531da8e8cf791c49caf0531f5dd1689bd91b");
  assert.equal(nodeSha("process.d.ts"),
    "42aaa94addeed66a04b61e433c14e829c43d1efd653cf2fda480c5fb3d722ed8");
  process.stdout.write("pinned Node declarations: bytes as reviewed\n");
}

{
  const jsonPath = resolve(here, "examples/collections-json.ts");
  const changedCopy = join(mkdtempSync(join(tmpdir(), "tscert-copy-")), "client.ts");
  writeFileSync(changedCopy, readFileSync(jsonPath, "utf8").replace("value, null", "null, value"));
  assert.throws(() => parseFile(changedCopy, false, libraryConfig, jsonPath),
    /gate:.*TypeScript client source bytes differ/);
  process.stdout.write("a copy other than the file TypeScript resolves: refused\n");
}

{
  const project = fixtureProject({
    "box.ts": "export interface Box { readonly flag: boolean; }\n",
    "barrel.ts": "export type { Box } from './box.js';\n",
    "global.d.ts": "interface GlobalBox { readonly flag: boolean; }\n",
    "other-global.d.ts": "interface GlobalBox { readonly other: number; }\n",
    "labeled.ts": "export interface Box { readonly other: number; }\n",
    "twice.ts": "export * from './box.js';\nexport * from './labeled.js';\n",
    "wrong.ts": "import type { Box } from './box.js';\nexport interface Wrong extends Box { readonly flag: string; }\n",
  });
  const ast = project.parse('import type { Box } from "@fixture/barrel";\n' +
    "export function read(box: Box, global: GlobalBox): boolean { return box.flag && global.flag; }\n");
  const root = must(ast.declarations.roots[0], "the barrel's name");
  assert.equal(root.declaration.module, "box.ts");
  assert.equal(root.binding.kind === "import" && root.binding.specifier, "@fixture/barrel");
  // A second global declaration merges with the first, as TypeScript merges
  // it: one equation with both declarations' members, identified by the first.
  const global = must(ast.declarations.definitions.find((d) => d.declaration.name === "GlobalBox"), "GlobalBox");
  assert.equal(global.declaration.module, "global.d.ts");
  assert(global.expression.k === "object");
  assert.deepEqual(global.expression.fields.map((f) => f.name), ["flag", "other"]);
  // Two star reexports of one name: TypeScript reports TS2308 on the barrel
  // (and would bind the first); the import is refused there.
  assert.throws(() => project.graphOf('import type { Box } from "@fixture/twice";'),
    /TypeScript reports an error in twice.ts on the path to Box: .*already exported a member named 'Box'/);
  // An interface TypeScript rejects is not a contract: refused, not interpreted
  // as the empty conjunction of its incompatible fields.
  assert.throws(() => project.graphOf("import type { Wrong } from './wrong.js';"),
    /TypeScript reports an error in wrong.ts#Wrong: .*incorrectly extends/);
  process.stdout.write("imports resolved as TypeScript binds them; TypeScript's errors on their path refused\n");
}

{
  const arrays = join(here, "examples", "values.ts");
  const doc = collectDeclarations(arrays, { arrays: [0, 0] });
  const proto = doc.definitions.find(d => d.declaration.module === "tscert/array-prototype");
  assert(proto && proto.expression.k === "object");
  // A computed key is the symbol it names: `[Symbol.iterator]` is `Symbol.iterator`.
  const keyText = (name: string | { symbol: number }) =>
    typeof name === "string" ? name : `[Symbol.${doc.symbols[name.symbol]?.name}]`;
  const methods = proto.expression.fields.filter(f => !f.optional);
  assert.deepEqual(methods.map(f => keyText(f.name)), arrayOverlay.map(e => e.name));
  const absentHooks = proto.expression.fields.filter(f => f.optional);
  assert.equal(absentHooks.length, 1);
  assert.equal(keyText(must(absentHooks[0], "conversion hook absence").name), "[Symbol.toPrimitive]");
  assert(absentHooks.every(f => f.readonly && f.type.k === "atom" && f.type.name === "undefined"));
  for (const field of methods) {
    const entry = arrayOverlay.find(e => e.name === keyText(field.name));
    // The member's own binders lead; the element binder `T` is last.
    assert(field.readonly && field.type.k === "scheme" && field.type.binders.at(-1)?.name === "T");
    const first = field.type.signatures[0];
    const receiver = first?.k === "function" ? first.receiver : null;
    assert(receiver?.k === "array" && receiver.element.k === "binder");
    assert.equal(receiver.readonly, entry?.from === "ReadonlyArray", `${String(field.name)} receiver`);
  }
  const changed = arrayOverlay.map(e => e.name === "reduce"
    ? { ...e, signature: e.signature.replace("initialValue: U", "initialValue?: U") } : e);
  assert.throws(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: changed }),
    /is not declared as reviewed/);
  const unsound = [{ name: "reduce", from: "ReadonlyArray" as const,
    signature: "reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T): T;" }];
  assert.doesNotThrow(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: unsound }),
    "the overlay, not the declaration reader, decides which overloads are trusted");
  // A member the project's library does not declare is absent, not refused.
  const absent = collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: [
    { name: "notDeclared", from: "ReadonlyArray", signature: "notDeclared(): T;" }] });
  const absentProto = absent.definitions.find(d => d.declaration.module === "tscert/array-prototype");
  assert(absentProto?.expression.k === "object" && absentProto.expression.fields.length === 0);
  closeParser();
  process.stdout.write("array prototype: overlay members read from TypeScript's declarations\n");
}

{
  for (const [file, call] of [
    ["invalid-native-find-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-native-map-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-native-join-coercion", "wrong({ value: 0 })"],
    ["invalid-native-sort-coercion", "wrong({ value: 0 })"],
    // What `%Iterate:ForIn%`'s step read is not what a later read finds.
    ["invalid-for-in-entry-call", "wrong({ a: 1 }, (v) => { delete v.a; })"],
    ["invalid-for-in-entry-field", "wrong({ inner: { a: 1, b: 2 } }, {})"],
    ["invalid-for-in-entry-rebound", "wrong({ a: 1, b: 2 }, {})"],
    // A function's `length` is not enumerable: its copy lacks it.
    ["invalid-spread-function-length", "arity((a, b) => a + b)"],
  ])
    assert.equal(runExample(file, call), undefined,
      `${file}: the actual source returns undefined despite its number contract`);
  assert.equal(runExample("native-sort-contracts", "noCoercion({ value: 7 })"), 7,
    "an explicit comparator never invokes the element's invalid conversion method");
  // A spread copies an own enumerable symbol-keyed property, which a type
  // stating no symbol key says nothing of.
  assert.equal(runExample("invalid-object-spread-symbol-index", `const s = Symbol();
    typeof open({ [s]: "x" })[s]`), "string",
    "invalid-object-spread-symbol-index: the copy holds a string under a symbol its type says holds a number");
  // A spread of a string copies its code units at its indices; of a class
  // value, its static fields.
  assert.equal(runExample("spread-string-class", `JSON.stringify([afterSpread(), afterClass()])`),
    '[{"a":""},{"x":1,"b":2}]', "spread-string-class: the copies JavaScript makes");
  assert.equal(runExample("invalid-spread-string-index", `typeof overIndex("x")[0]`), "string",
    "invalid-spread-string-index: the string's code unit overwrites the number under `0`");
  assert.equal(runExample("invalid-spread-class-static", `class D { static a = "s"; }
    typeof overStatic(D).a`), "string",
    "invalid-spread-class-static: the class's static field overwrites the number under `a`");
  // A class value's own enumerable properties are its own static fields: a
  // copy, a rest and `Object.assign` take those, not its base's, which it
  // reads through its prototype and `for...in` visits; no static method.
  assert.equal(runExample("class-static-inheritance", `JSON.stringify([copy(), rest(), keys(), Derived.inherited])`),
    '[{"own":2,"two":3},{"two":3},"own,two,inherited,",1]', "class-static-inheritance: the copies JavaScript makes");
  assert.equal(runExample("invalid-class-static-inherited-copy", `String(copy().inherited)`), "undefined",
    "invalid-class-static-inherited-copy: the copy lacks the base's static field");
  assert.equal(runExample("invalid-class-static-inherited-rest", `String(rest().inherited)`), "undefined",
    "invalid-class-static-inherited-rest: the rest lacks the base's static field");
  assert.equal(runExample("invalid-class-static-method-copy", `typeof copy().m`), "undefined",
    "invalid-class-static-method-copy: the copy lacks the static method");
  assert.equal(runExample("invalid-class-static-assign", `JSON.stringify(assign())`), '{"own":2}',
    "invalid-class-static-assign: Object.assign copies the own static field only");
  assert.equal(runExample("invalid-typeof-inherited-statics", `String(make().inherited)`), "undefined",
    "invalid-typeof-inherited-statics: the returned class lacks the inherited static TypeScript promises");
  // External code receiving a class value may write its static field; the
  // test supplies `change`, which the example declares.
  assert.equal(runExample("invalid-class-static-generic-external", `function change(k) { k.limit = 9; }
    run()`), 9, "invalid-class-static-generic-external: the read finds the written value");
  assert.equal(runExample("class-static-variadic", `JSON.stringify([run, copy()])`), "[19,7]",
    "class-static-variadic: the construction and the copy JavaScript makes");
  // A write at a string key known only at run time: `__proto__` runs the
  // prototype's setter where the object does not own the key, which with a
  // number changes nothing, and writes the property where it owns it; with an
  // object value the setter replaces the prototype, which the pipeline refuses.
  assert.equal(runExample("computed-key-write", `JSON.stringify([
    Object.keys(dictionary("__proto__")).length,
    Object.getPrototypeOf(dictionary("__proto__")) === Object.prototype,
    copied(JSON.parse('{"__proto__": 1}'), "__proto__")["__proto__"],
    Object.keys(multiLiteral("b")), Object.keys(numberKey(1.5))])`), '[0,true,5,["b"],["1.5"]]',
    "computed-key-write: JavaScript's write, which the lowering's dispatch and copies follow");
  assert.equal(runExample("computed-key-proto-refused", `typeof setProto("__proto__").a`), "string",
    "computed-key-proto-refused: the setter makes the object value the prototype, whose string the dictionary reads");
  // Object.assign writes a function's `name`, which is not writable: it throws.
  assert.throws(() => runExample("invalid-function-fields-inferred", "named()"), /read only property 'name'/);
  // A dictionary beside an array: TypeScript types its `length` `number`, and
  // an empty one has none.
  assert.equal(runExample("invalid-length-array-or-dictionary", "size({})"), undefined,
    "invalid-length-array-or-dictionary: the actual source returns undefined despite its number contract");
  // A view of `length` reads an array's store length, after a push too.
  assert.equal(runExample("length-view", "lengths([4]) + grown(0)"), 9,
    "length-view: one, three, two and one, then two after the push");
  // A mutable tuple's `length` grows past its arity.
  assert.equal(runExample("invalid-length-view-tuple", "tupleLength(0)"), 2,
    "invalid-length-view-tuple: the view reads 2 despite its 1 contract");
  // A literal inherits `Object.prototype`'s members.
  assert.equal(runExample("invalid-dictionary-inherited-key", `typeof inherited("toString")`), "function",
    "invalid-dictionary-inherited-key: the read finds Object.prototype.toString despite its number contract");
  // A member access, an optional field and a pattern each find
  // `Object.prototype`'s member under its name where the object lacks it.
  assert.equal(runExample("invalid-dictionary-inherited-named", "typeof named()"), "function",
    "invalid-dictionary-inherited-named: the read finds Object.prototype.__defineGetter__");
  assert.equal(runExample("invalid-word-count", "next({}, \"constructor\")"), "function Object() { [native code] }1",
    "invalid-word-count: the count of `constructor` is a string");
  assert.equal(runExample("invalid-optional-inherited-key", "typeof optional({})"), "function",
    "invalid-optional-inherited-key: the read finds Object.prototype.toString");
  assert.equal(runExample("invalid-pattern-inherited-key", "typeof destructured({})"), "function",
    "invalid-pattern-inherited-key: the pattern finds Object.prototype.valueOf");
  // A non-null assertion on a read the object lacks the key of.
  assert.equal(runExample("invalid-non-null-index", "wrong({}, 0)"), undefined,
    "invalid-non-null-index: the read is undefined despite the assertion");
  // A callee generic over `Array<A>` reverses a tuple found in `unknown`.
  assert.throws(() => runExample("invalid-open-array-generic-call", "caller()"), /toFixed is not a function/);
  // An array's `length` is not one of its own enumerable properties.
  assert.equal(runExample("invalid-array-spread-length", "count([1, 2])"), undefined,
    "invalid-array-spread-length: the copy has no length despite its number contract");
  // `Array.isArray` on `unknown`: TypeScript reads the array as `any[]`.
  assert.equal(runExample("invalid-isarray-unknown-element", `typeof head(["a"])`), "string",
    "invalid-isarray-unknown-element: the actual source returns a string despite its number contract");
  assert.equal(runExample("invalid-isarray-unknown-push", `const a = ["a"]; grow(a); typeof a[1]`), "number",
    "invalid-isarray-unknown-push: a number lands in an array of strings");
  // A rest typed by an intersection: TypeScript accepts the call at an instance
  // where the declared contract holds no array, and the result is no boolean.
  assert.equal(runExample("invalid-rest-intersection", "typeof wrong()"), "number",
    "invalid-rest-intersection: the actual source returns a number despite its boolean contract");
  // A rest typed by a type parameter typing a value too: TypeScript infers a
  // tagged instance, and the collected array returned at it has no tag.
  assert.equal(runExample("invalid-rest-pack-value", "typeof wrong()"), "undefined",
    "invalid-rest-pack-value: the actual source returns undefined despite its string contract");
  // Forwarding through an ordinarily annotated binding does not prevent the
  // callback from shortening the source; the final map position remains a hole.
  assert.equal(runExample("invalid-callback-effect-forwarding",
    "const result = wrong([1, 2]); JSON.stringify([result.length, 0 in result, 1 in result])"), "[2,true,false]");
  // Reading a hole gives undefined, so it satisfies the input annotation. map
  // skips it even when the callback preserves the heap and returns a number.
  assert.equal(runExample("invalid-map-hole-coalescing", `const xs = [1, 2]; delete xs[1];
    const result = coalescingCallback(xs); JSON.stringify([result.length, 1 in result, result[1]])`), "[2,false,null]");
  // A key added in place is seen by every reference to the object, at its own
  // type: through a parameter (TypeScript accepts the module), through a
  // constant bound to the object, through a destructured binding.
  assert.equal(runExample("invalid-key-adding-parameter-write", "seen"), "number number");
  // A call between the write and the default stores a string in the cell.
  assert.equal(runExample("invalid-array-read-cell-call", "typeof clobbered()"), "string",
    "invalid-array-read-cell-call: the actual source returns a string despite its number contract");
  for (const [file, call] of [["invalid-object-growth-alias", "grow()"],
    ["invalid-object-growth-reused-name", "reusedName()"], ["invalid-computed-key-alias", `grow("x")`]] as const)
    assert.throws(() => runExample(file, call), /toUpperCase is not a function/,
      `${file}: the actual source reads the added number as a string`);
  // A function the caller supplies may own a `call` property: `.call` of it
  // is not the standard method, so the gate refuses these sources.
  assert.equal(runExample("invalid-call-provenance-spread",
    `overridden({ read: Object.assign(function () { return 1; }, { call: () => "wrong" }) }, { value: 1 })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-assign",
    `probe(Object.assign(() => 1, { call: () => "wrong" }))`), "wrong");
  assert.equal(runExample("invalid-call-provenance-escape",
    `probe((f) => { Object.assign(f, { call: () => "wrong" }); })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-module-argument",
    `probe((f) => { Object.assign(f, { call: () => "wrong" }); })`), "wrong");
  // An importing module's write, made before it calls `probe`.
  assert.equal(runExample("invalid-call-provenance-module-export",
    `Object.assign(g, { call: () => "wrong" }); probe()`), "wrong");
  assert.equal(runExample("invalid-direct-eval", "probe()"), "wrong");
  assert.equal(runExample("invalid-call-provenance-shadow-loop",
    `probe([Object.assign(() => 1, { call: () => "wrong" })])`), "wrong");
  assert.equal(runExample("invalid-call-provenance-shadow-catch",
    `probe(() => { throw Object.assign(() => 1, { call: () => "wrong" }); })`), "wrong");
  // Run as a script: `g` is the global object's property. Another script's
  // write through it is what the trusted assumption that only the file
  // writes its top-level bindings excludes.
  assert.equal(runExample("script-global-assumption",
    `probe(() => { globalThis.g.call = () => "wrong"; })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-let",
    `reassigned(Object.assign(function () { return 1; }, { call: () => "wrong" }), { value: 1 })`), "wrong");
  // Sloppy code converts a receiver that is not an object: a primitive to a
  // wrapper object, `undefined` to the global object. The pipeline refuses
  // sloppy code reading `this` at such a receiver type.
  assert.equal(runExample("sloppy-this-primitive-refused", "typeof caller()"), "object",
    "sloppy-this-primitive-refused: the actual source returns a String object despite its string contract");
  assert.equal(runExample("sloppy-this-closure-refused", "typeof count()"), "undefined",
    "sloppy-this-closure-refused: the actual source reads the global object despite its number contract");
  // A subclass of Array is its instances' `constructor`, so `map` constructs
  // its result through the subclass (ArraySpeciesCreate): the construction the
  // ordinary array construction assumption excludes, and why the pipeline
  // refuses the class (`invalid-array-subclass`).
  assert.equal(runExample("invalid-array-subclass", `let built = 0;
    class Loud extends Counted { constructor(...args) { super(...args); built++; } }
    const xs = Loud.from([1, 2]); built = 0;
    const result = doubled(xs);
    JSON.stringify([result instanceof Loud, built, Array.from(result)]);`), "[true,1,[2,4]]");
  // An enum member known only at run time: its reverse mapping replaces a
  // member named by its value's key; a member read before it is written is
  // undefined, through a closure or a module function; its value is a
  // number, not a literal.
  assert.equal(runEmitted("invalid-enum-computed-nan-name", "one()"), "X");
  assert.equal(runEmitted("invalid-enum-computed-forward", "first()"), undefined);
  assert.equal(runEmitted("invalid-enum-computed-call-order", "first()"), undefined);
  assert.equal(runEmitted("invalid-enum-computed-literal", "wrong()"), 2);
  assert.equal(runEmitted("invalid-enum-proto-member", "proto() === Object.prototype"), true);
  // Exact observation uses the native identity and ordinary constructor.
  // A fulfilled record may acquire a then member before it is observed.
  assert.equal(await runExample("native-promise-record-observation", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    const observed = [await read(p), await readAll([p]), (await gather([p]))[0].n];
    Object.assign(p, { constructor: undefined });
    const changed = [await read(p), await readAll([p]), (await gather([p]))[0]];
    return JSON.stringify([observed, changed]);
  })()`), "[[1,1,1],[null,null,42]]");
  // A genuine native subclass has no own constructor, but its inherited
  // constructor differs from the current realm's ordinary Promise.
  assert.equal(await runExample("native-promise-record-observation", `(async () => {
    class Derived extends Promise {}
    const record = { n: 1 };
    const p = new Derived(resolve => resolve(record));
    Object.assign(record, { then: resolve => resolve(42) });
    return JSON.stringify([p instanceof Promise, Object.hasOwn(p, "constructor"), await read(p)]);
  })()`), "[true,false,null]", "native identity and own-key exclusion also require the standard inherited constructor");
  // Reaction construction observes Symbol.species. External changes to it
  // execute construction outside the reviewed native operation's contract.
  assert.equal(await runExample("native-promise-reactions", `(async () => {
    let constructions = 0;
    class Counted extends Promise { constructor(executor) { super(executor); constructions++; } }
    const p = Promise.resolve(3);
    Object.defineProperty(Promise, Symbol.species, { value: Counted });
    const result = await finalized(p);
    return JSON.stringify([result, constructions > 0]);
  })()`), "[3,true]", "the host premise fixes standard species behavior for reaction construction");
  assert.equal(await runExample("invalid-native-promise-constructor-intersection", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    Object.assign(p, { constructor: Promise });
    return await modifyAndRead(p);
  })()`), undefined,
    "the actual constructor write through a typed structural alias invalidates the numeric result");
  // Native catch and finally construct a promise that re-adopts the payload.
  for (const file of ["invalid-native-promise-catch-record", "invalid-native-promise-catch-record-explicit", "invalid-native-promise-finally-record"])
    assert.equal(await runExample(file, `(async () => {
      const record = { n: 1 };
      const p = Promise.resolve(record);
      Object.assign(record, { then: resolve => resolve(42) });
      return await forward(p);
    })()`), 42, `${file}: native result construction adopts the record's added then member`);
  assert.equal(await runExample("native-promise-reactions", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    return JSON.stringify([await caught(Promise.resolve(2)), await finalized(Promise.resolve(3)), await mapped(p), await finalizedPromise(Promise.resolve(4), p)]);
  })()`), "[2,3,1,4]");
  // The external callback returns without mutating the cell. Only the hidden
  // then hook, absent from its open record contract, corrupts the typed cell.
  assert.equal(await runExample("invalid-native-promise-finally-cleanup", `
    function callbackResult(cell) {
      return { tag: 1, then(resolve) { cell.value = "changed"; resolve(undefined); } };
    }
    forward(Promise.resolve(4), { value: 1 });`), "changed",
    "finally cannot invoke an unconstrained cleanup result's hidden then hook");
  assert.equal(await runExample("invalid-native-promise-augmentation", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    Object.assign(p, { constructor: Promise });
    return await read(p);
  })()`), undefined, "a source merge cannot relax the native constructor invariant");
  assert.equal(runExample("invalid-native-promise-extra-field", "ownValue()"), undefined,
    "a source merge cannot manufacture fields on an async function's native promise result");
  assert.equal(await runExample("native-promise-catch-explicit", `caughtString(Promise.reject("failure"))`), "fallback");
  assert.equal(runExample("invalid-native-promise-copy", "fake(Promise.resolve(1)).then"), undefined,
    "a source spread copies no inherited native promise methods");
  assert.equal(runExample("native-promise-constructor-read", "constructorValue(Promise.resolve(1)) === Promise"), true,
    "excluding an own constructor keeps the inherited native constructor observable");
  assert.equal(await runExample("native-promise-qualified-return", `(async () => {
    let adoptedElements = 0;
    const element = { then(resolve) { adoptedElements++; resolve(42); } };
    const array = [element];
    const record = { tag: 1, then: 0 };
    return JSON.stringify([
      await stable(2), await fromNumber(3), await fromNative(Promise.resolve(4)),
      await stableUnknown(5), await adoptUnknown(Promise.resolve(6)),
      await stableArray(array) === array, await adoptArray(Promise.resolve(array)) === array,
      await resolvedArray(array) === array, await stableRecord(record) === record,
      widenResult(wrap) === wrap, adoptedElements
    ]);
  })()`), "[2,3,4,5,6,true,true,true,true,true,0]",
    "stable generic resolution preserves its payload, and resolving an array does not adopt its elements");
  assert.equal(await runExample("invalid-native-promise-qualified-view", `
    unstableView({ tag: 1, then(resolve) { resolve(42); } });`), 42,
    "an open record view does not establish the explicit non-thenable bound used by fresh resolution");
  // PromiseResolve's native branch returns the same promise even if its
  // fulfilled record later acquires then. Its mixed fresh branch admits a
  // primitive, and a stable record's explicit bound preserves its identity.
  assert.equal(await runExample("native-promise-resolve-identity", `(async () => {
    let adopted = 0;
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { adopted++; resolve(42); } });
    const stable = { tag: 1, then: 0 };
    return JSON.stringify([nativeIdentity(p) === p, nativeWiden(p) === p,
      mixedIdentity(p) === p, await readIdentity(p), adopted,
      await mixedIdentity(2), await freshStable(stable) === stable]);
  })()`), "[true,true,true,1,0,2,true]",
    "native resolution observes its existing payload through constructor identity");
  assert.equal(await runExample("invalid-native-promise-async-record-forward", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { resolve(42); } });
    return await forward(p);
  })()`), 42, "fresh async forwarding re-adopts the native promise's fulfilled record");
  assert.equal(await runExample("invalid-native-promise-resolve-receiver", `class Other extends Promise {}
    (async () => {
    const cell = { value: 1 };
    const record = { tag: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { cell.value = "changed"; resolve(42); } });
    return await forward(p, cell);
  })()`), "changed", "a different PromiseResolve receiver constructs and adopts instead of taking native identity");
  for (const [file, fn, native] of [
    ["invalid-native-promise-async-unknown-value", "openValue", false],
    ["invalid-native-promise-async-unknown-native", "openNative", true],
    ["invalid-native-promise-resolve-input", "openResolve", false],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const cell = { value: 1 };
      const record = {};
      const input = ${native ? "Promise.resolve(record)" : "record"};
      Object.assign(record, { then(resolve) { cell.value = "changed"; resolve(42); } });
      await ${fn}(input);
      return cell.value;
    })()`), "changed", `${file}: widening the result leaves the hidden then hook's heap effect observable`);
  // These values and the wrapper execute in the same realm. An array is a
  // stable resolution input even when its elements contain then hooks.
  assert.equal(await runExample("generic-promise-resolution", `(async () => {
    let elementAdoptions = 0;
    const values = [{ then(resolve) { elementAdoptions++; resolve(42); } }];
    let finish;
    const pending = new Promise(resolve => { finish = resolve; });
    const waiting = repeated(pending);
    finish(9);
    let rejected = false;
    try { await repeated(Promise.reject("expected")); }
    catch (reason) { rejected = reason === "expected"; }
    return JSON.stringify([
      await numeric(1), await stored(2), await aliasWrap(3),
      await native(Promise.resolve(4)), await repeated(Promise.resolve(5)),
      await array(values) === values, await union(Promise.resolve(values)) === values,
      await waiting, rejected, elementAdoptions, await forward(Promise.resolve(Promise.resolve(10))),
    ]);
  })()`), "[1,2,3,4,5,true,true,9,true,0,10]",
    "qualified wrapper forwarding preserves stable arrays, native fulfillment, rejection and pending resolution");
  assert.equal(runExample("generic-promise-associated-result", `
    const cell = { value: 6 };
    JSON.stringify([accept(7), exchange(cell, 8), cell.value]);`), "[7,6,8]",
    "associated-result storage keeps the numeric input and write contract");
  // An open record, a native promise of one, or a union with one, is
  // adopted where it holds a then hook: the wrapper does not settle to it.
  for (const [file, fn, input] of [
    ["invalid-generic-promise-open-record", "openRecord", "record"],
    ["invalid-generic-promise-open-native", "openNative", "Promise.resolve(record)"],
    ["invalid-generic-promise-open-union", "openUnion", "record"],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const record = { n: 1 };
      const input = ${input};
      Object.assign(record, { then(resolve) { resolve(42); } });
      return await ${fn}(input);
    })()`), 42, `${file}: the open record's then hook is adopted, not settled to`);
  // The ambient wrapper implemented as `Promise.resolve`, which TypeScript
  // accepts at the declaration, adopts the open record's then hook too.
  assert.equal(await runExample("invalid-generic-promise-ambient-open-record", `
    function wrap(value) { return Promise.resolve(value); }
    (async () => {
    const record = { n: 1 };
    Object.assign(record, { then(resolve) { resolve(42); } });
    return await openRecord(record);
  })()`), 42, "an ambient Awaited<T> wrapper adopts the open record's then hook");
  assert.equal(await runExample("invalid-generic-promise-erased-call", `(async () => {
    const cell = { value: 1 };
    await erasedCall({ n: 1, then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "a widened result does not constrain the adopted then hook's heap effect");
  assert.equal(await runExample("invalid-generic-promise-observed-input", `(async () => {
    return typeof (await unwrap(Promise.resolve(1)));
  })()`), "number", "the observation of a promise is its payload, not the promise");
  assert.equal(await runExample("generic-promise-resolvable", `(async () => JSON.stringify([
    await numeric(1), await native(Promise.resolve(2)), await union(Promise.resolve("3")),
    await settleUnknown(Promise.resolve(4)),
  ]))()`), '[1,2,"3",4]', "an explicitly qualified parameter settles as an implied one");
  assert.equal(await runExample("invalid-generic-promise-resolvable-result", `(async () => {
    return typeof (await settle(Promise.resolve(1)));
  })()`), "number", "a qualified parameter's result is not the parameter: a promise argument resolves");
  assert.equal(await runExample("invalid-generic-promise-resolvable-local", `(async () => {
    const cell = { value: 1 };
    await settle({ then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "an ordinary bound named Resolvable does not constrain a hidden then hook");
  // An awaitable parameter is observed, never resolved again: a record that
  // acquires a then hook after its promise fulfilled is awaited as itself,
  // while returning it, or the promise, from an async function adopts it.
  assert.equal(await runExample("generic-promise-awaitable", `(async () => {
    const cell = { value: 1 };
    const box = { n: 1 };
    const input = Promise.resolve(box);
    await input;
    Object.assign(box, { then(resolve) { cell.value = "changed"; resolve(42); } });
    return JSON.stringify([await record(input), await numeric(2), await native(Promise.resolve(3)),
      await union(input), await union(4), cell.value]);
  })()`), "[null,null,null,null,null,1]", "awaiting an awaitable parameter observes it without adopting a later then hook");
  for (const [file, fn] of [
    ["invalid-generic-promise-awaitable-result", "settle"],
    ["invalid-generic-promise-awaitable-observation", "settle"],
    ["invalid-generic-promise-awaitable-return", "forward"],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const cell = { value: 1 };
      const box = { n: 1 };
      const input = Promise.resolve(box);
      await input;
      Object.assign(box, { then(resolve) { cell.value = "changed"; resolve(42); } });
      return JSON.stringify([await ${fn}(input), cell.value]);
    })()`), '[42,"changed"]', `${file}: async return resolves the observation again, adopting its then hook`);
  assert.equal(await runExample("invalid-generic-promise-awaitable-local", `(async () => {
    const cell = { value: 1 };
    await settle({ then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "an ordinary bound named Awaitable does not constrain a hidden then hook");
  assert.equal(await runExample("invalid-generic-promise-unknown-output", `(async () => {
    const cell = { value: 1 };
    const input = { n: 1, then(resolve) { cell.value = "changed"; resolve(42); } };
    await erasedOutputCall(input);
    return cell.value;
  })()`), "changed", "an unknown generic output does not constrain a hidden then hook's heap effect");
  // A function value known only by its type may read a position its type
  // does not mention: `map` passes `g` the index, which `g` returns.
  assert.equal(runExample("invalid-named-function-arity-value", "JSON.stringify([main(), typeof main()[0]])"), '[[0],"number"]',
    "a callback typed (x: number) => string reads the index map passes");
  process.stdout.write("native-contract counterexamples run under Node: as the contracts say\n");
}

{
  for (const [file, expression, expected] of [
    ["loose-equality", "[samePrimitive(false, ''), samePrimitive(null, undefined), samePrimitive(9007199254740993n, 9007199254740992), platform('native')].join()", "true,true,false,native"],
    ["loose-equality", "const box = {value: 0}; const result = evaluatedOperands(box, '1'); JSON.stringify([result, box.value])", "[true,1]"],
    ["loose-equality", "const xs = []; [differentArrays(xs, xs), readonlyIdentity(xs, []), namedNullish({valueOf(){throw Error('called')}}, null)].join()", "false,false,false"],
    ["invalid-loose-equality-narrowing", "typeof wrongNumber('1', 1)", "string"],
    ["loose-equality-array-conversion-refused", "const xs = [1]; let calls = 0; xs.valueOf = () => { calls++; return 2; }; JSON.stringify([arrayConversion(xs, 2), calls])", "[true,1]"],
    ["callable-bag-union", "[readWrite(true, true), readWrite(false, true)].join()", "false,false"],
    ["invalid-callable-bag-union", "wrong(false, true)", false],
    ["recursive-callable", "selfLoop()", false],
    ["invalid-recursive-callable", "wrong()", true],
    ["non-regular-alias", "first({ v: 1, next: null })", 1],
    ["invalid-non-regular-alias", "wrong({ v: 1, next: null })", null],
    ["assertion-snapshot", "assertedSnapshot({ value: 3 })", 3],
    ["saved-field-comparison", "const box = { value: 7 }; JSON.stringify([comparedBeforeWrite(box), box.value])", "[true,null]"],
    ["array-assign-field-target", "const pair = { first: 1, second: 2 }; const rest = { items: [] }; JSON.stringify([swapInto(pair, rest), pair, rest.items])", '[5,{"first":2,"second":2},[3,4]]'],
    ["array-assign-field-target", "const box = { slot: 'x' }; JSON.stringify([keyBeforeRead({ order: '' }, box), box.slot])", '["kd","kd"]'],
    // The array's iterator stays finished once a step found the end: a later
    // step finds it finished though code grew the array in between.
    ["array-pattern-exhausted-refused", "holeThenGrow()", 9],
    ["array-pattern-exhausted-rest-refused", "JSON.stringify(restAfterGrow())", "[9]"],
    ["array-binding-exhausted-refused", "defaultGrows()", 100],
    ["array-pattern-steps", "JSON.stringify([freshSource({ slot: 0 }, { n: 0 }), heldSource([], { first: 0, second: 0 }), heldSource([5, 6, 7, 8], { first: 0, second: 0 }), boundDefaults([]), boundDefaults([4, 5, 6, 7])])", "[10,6,19,2,11]"],
    ["instanceof-unknown-refused", "typeof px(Object.create(Point.prototype))", "undefined"],
    ["invalid-call-own-override", "JSON.stringify(copyReaderArgument({ read: Object.assign(function () { return this.value; }, { call() { return 'wrong'; } }) }, new PrototypeReader()))", '"wrong"'],
    ["invalid-spread-symbol-nonenumerable", "const input = {}; Object.defineProperty(input, sym, { value: 1, writable: true, enumerable: false }); const out = symbolBranch(input); JSON.stringify([input[sym], sym in out, 'b' in out])", "[1,false,false]"],
    ["relational-conversion", "JSON.stringify([negativeFirst([]), negativeFirst([-1]), belowLimit(1, 2n)])", "[false,true,true]"],
    ["relational-boolean-comparison", "JSON.stringify([order(false, true), order(true, false), atMostTrue(true)])", "[true,false,true]"],
    ["saved-field-comparison", "currentAfterWrite({ value: 7 })", null],
    ["invalid-saved-field-comparison", "wrong({ value: 7 })", null],
    // A closure reads a captured cell when it runs, and sees its own write.
    ["invalid-closure-graph-captured-cell", "counter()", null],
    // A closure created before a write, or an iteration before one, reads
    // the written value; a throw after a write leaves the try with it.
    ["invalid-capture-before-write", "String(stale()())", "undefined"],
    ["invalid-capture-next-iteration", "String(loopCapture(2)())", "undefined"],
    ["invalid-slot-catch-entry", "midTry('a', 'b', () => { throw 1; })", "b"],
    ["slot-object-growth", "JSON.stringify(grownSlot('x', false)()) + JSON.stringify(grownSlot('x', true)())", "{\"x\":1,\"count\":2}{\"x\":1,\"count\":2}"],
    ["invalid-evolving-use-contract", "build(6)", "many"],
    ["invalid-generic-callee-use-contract", "count(3).head", "many"],
    ["generic-callee-use-contract", "JSON.stringify(fromArray(1, 2))", "{\"head\":1,\"tail\":{\"head\":2,\"tail\":null}}"],
    ["evolving-use-contract", "JSON.stringify(reverse({ head: 1, tail: { head: 2, tail: null } }))", "{\"head\":2,\"tail\":{\"head\":1,\"tail\":null}}"],
    ["activation-slots", "[survivesCall('a', 'b', () => { throw 1; }), absorbedInnerTry('a', 'b', () => { throw 1; }), capturedAfterWrites(false)(), JSON.stringify(reverse({ head: 1, tail: { head: 2, tail: null } }))].join()", "a,a,no,{\"head\":2,\"tail\":{\"head\":1,\"tail\":null}}"],
    // A generic function type's result: a pair where it holds, the argument
    // itself where another scheme was passed for it.
    ["generic-function-type-member", "pass({ twice: () => (x) => [x, x] }).twice()(1).join()", "1,1"],
    ["invalid-generic-function-type-member", "wrong({ twice: () => (x) => x }).twice()(1)", 1],
    // A generic function type in an annotation: a value of it is used at an
    // instance; another scheme, a narrower bound or a constant result gives a
    // value outside it there.
    ["generic-function-type-annotation", "[local(), bounded(), impredicative()].join()", "a,abc,1"],
    ["invalid-generic-function-type-annotation", "typeof wrong()", "string"],
    ["invalid-generic-function-type-bound", "typeof unbounded()", "number"],
    ["invalid-generic-closure-field", "typeof wrong()", "number"],
    ["invalid-generic-constructor-type", "typeof wrong()", "string"],
  ] as const)
    assert.equal(runExample(file, expression), expected, file);
  // Imported unique symbols as Node's modules give them: a re-export is the
  // symbol it re-exports, and two constants made by `Symbol.for` of one
  // string hold one symbol; `Symbol()` makes another.
  assert.equal(runImporting("unique-symbol-reexport-value-import", "same()"), true);
  assert.equal(runImporting("unique-symbol-registry-value-import", "same()"), true);
  assert.equal(runImporting("invalid-unique-symbol-value-import", "held === brand"), false);
  // A class has no plain call: calling it throws.
  assert.throws(() => runExample("invalid-class-as-function", "go()"), /cannot be invoked without 'new'/);
  // A construction in a static initializer reads a static not yet defined.
  assert.equal(runExample("invalid-class-static-constructs-early", "String(read())"), "undefined");
  // A generic method's contract read as `unknown` admits 42, which no call
  // can run.
  assert.throws(() => runExample("invalid-generic-method-nested-scheme", "wrong().run({ id: (x) => x })"),
    /is not a function/);
  // The iterator protocol a program's iterable runs: its iterator's `return`
  // is called on `break`, `return` and a throw out of the body, and not at the
  // end or on `continue`; a throw out of the body wins over one out of the
  // close. The parser's lowering (`protocolForOf`) calls `return` exactly there.
  const list = "new LinkedList(new Cell(1, new Cell(5, new Cell(9, null))), { closed: 0 })";
  const closes = (call: string) =>
    runExample("for-of-program-iterable", `const l = ${list}; const r = ${call}; JSON.stringify([r, l.log.closed])`);
  assert.equal(closes("sum(l)"), "[15,0]");
  assert.equal(closes("firstAbove(l, 3)"), "[5,1]");
  assert.equal(closes("firstOver(l, 3)"), "[5,1]");
  assert.equal(closes("skipSmall(l, 3)"), "[14,0]");
  assert.equal(runExample("for-of-program-iterable",
    "const log = { closed: 0 }; JSON.stringify([firstEven(new Countdowns(5, log)), log.closed])"), "[4,1]");
  assert.equal(runExample("for-of-program-iterable", "bodyThrows(new Brittle()).message"), "body");
  process.stdout.write("examples run as JavaScript: results as their outcomes say\n");
}

{
  const good = run("values");
  const fragment: unknown = JSON.parse(readFileSync(join(good, "fragment.json"), "utf8"));
  assert.ok(fragment && typeof fragment === "object" && !Array.isArray(fragment));
  const forged = structuredClone(fragment);
  assert.ok("functions" in forged && Array.isArray(forged.functions));
  const first: unknown = forged.functions[0];
  assert.ok(first && typeof first === "object" && "retType" in first);
  const ast = join(good, "raw-graph-annotation.json");
  // The source states type terms: neither a graph label nor a claim. The
  // producer's own claims are offered, so the refusal is the annotation's.
  for (const [retType, refusal] of [
    [{ a: "graph", label: 4 }, /source cannot state an internal graph label/],
    [{ top: false, atoms: [{ a: "boolean" }] }, /a source annotation is a type term, not a claim/],
  ] as const) {
    Object.assign(first, { retType });
    writeFileSync(ast, JSON.stringify(forged));
    const produced = produceWith(good, join(good, "claims.json"), "raw-graph", ast);
    assert.equal(produced.status, 1);
    assert.match(produced.stderr, refusal);
  }
  const extraField = join(good, "extra-ast-field.json");
  writeFileSync(extraField, JSON.stringify({ ...fragment, unexamined: true }));
  assert.match(invoke(join(good, "claims.json"), join(good, "evidence.json"), good, extraField), /unexpected fields/);
  process.stdout.write("a graph label, a claim-shaped annotation and an unexamined field in the parser's document: refused\n");
}

{
  // Bypass the producer's refusal: manufacture its old proposal by erasing
  // the method in a copy of the AST. Both verifier entry points must still
  // refuse the ORIGINAL contract before accepting any such proposal/evidence.
  const erased = run("invalid-generic-contract-erasure");
  const ast: Ast = JSON.parse(readFileSync(join(erased, "fragment.json"), "utf8"));
  const declaration = ast.declarations?.definitions.find(d => d.declaration.name === "Witness");
  assert(declaration?.expression.k === "object");
  const member = declaration.expression.fields.find(f => f.name === "choose");
  assert(member?.type.k === "scheme");
  member.type = { k: "atom", name: "unknown", span: member.type.span };
  const weakened = join(erased, "weakened.json");
  writeFileSync(weakened, JSON.stringify(ast));
  const lowered = spawnSync(verifier, ["--lower-control-flow", weakened],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(erased, "weakened-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposal = spawnSync(producerExecutable, [weakened, flow],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(proposal.status, 0, proposal.stderr);
  const claims = join(erased, "forged-claims.json");
  const evidence = join(erased, "forged-evidence.json");
  writeFileSync(claims, proposal.stdout);
  writeFileSync(evidence, "{}");
  const searched = spawnSync(verifier, ["--produce-source-claims",
    join(erased, "fragment.json"), claims, join(erased, "source.ts"), evidence, "12"],
    { encoding: "utf8", timeout: 30_000 });
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /generic contract.*cannot be erased/);
  assert.match(invoke(claims, evidence, erased), /generic contract.*cannot be erased/);
}
{
  // A generic method's argument pack `P` beside a nested generic method
  // binding its own `P` is a pack: the inner `P` is that method's value binder.
  // The outer `P` used also as a value inside a nested method binding only `Q`
  // is refused, as no scheme states such a binder. An alias reaching itself
  // under no object, array, tuple or function type is refused where it is used.
  const span: [number, number] = [0, 0];
  const binder = (name: string): TypeTerm => ({ k: "binder", name, span });
  const method = (params: TypeTerm[], rest: TypeTerm | null, result: TypeTerm): Extract<TypeTerm, { k: "function" }> =>
    ({ k: "function", effect: "unrestricted", receiver: { k: "self", span }, params, rest, result, span });
  const scheme = (name: string, signature: Extract<TypeTerm, { k: "function" }>,
      bound: TypeTerm | null = null): TypeTerm =>
    ({ k: "scheme", binders: [{ name, bound, default: null, resolution: null, span }], signatures: [signature], span });
  const runner = (inner: TypeTerm): TypeTerm => scheme("P", method(
    [{ k: "object", fields: [{ name: "id", optional: false, readonly: true, type: inner, span }],
      stringIndex: null, calls: [], span }],
    { k: "pack", of: binder("P"), span }, { k: "atom", name: "number", span }),
    { k: "array", presence: "readable", readonly: false, element: { k: "atom", name: "unknown", span }, span });
  const forgeDefinition = (artifacts: string, name: string, file: string, change: (d: TypeDefinition) => void) => {
    const fragment: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
    change(must(fragment.declarations.definitions.find((d) => d.declaration.name === name), name));
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    const searched = produceWith(artifacts, join(artifacts, "claims.json"), file, path);
    return { status: searched.status, detail: searched.stdout + searched.stderr };
  };
  const withRun = (inner: TypeTerm) => (d: TypeDefinition) => {
    assert(d.expression.k === "object");
    must(d.expression.fields[0], "Runner's method").type = runner(inner);
  };
  const schemeHost = run("scheme-binder-roles");
  const shadowed = forgeDefinition(schemeHost, "Runner", "forged-shadowed-pack",
    withRun(scheme("P", method([binder("P")], null, binder("P")))));
  assert.equal(shadowed.status, 0, shadowed.detail);
  const mixed = forgeDefinition(schemeHost, "Runner", "forged-mixed-pack",
    withRun(scheme("Q", method([binder("Q"), binder("P")], null, binder("Q")))));
  assert.equal(mixed.status, 1);
  assert.match(mixed.detail, /Runner: generic contract at \[0,0\]: a binder used as both a value and an argument pack is not represented/);
  const unguarded = forgeDefinition(run("non-regular-alias"), "Box", "forged-unguarded-alias", (d) => {
    assert(d.expression.k === "object");
    const next = must(d.expression.fields.find((f) => f.name === "next"), "Box's next").type;
    assert(next.k === "union");
    d.expression = { k: "union", parts: [{ k: "parameter", index: 0, span }, must(next.parts[0], "Box<[T]>")], span };
  });
  assert.equal(unguarded.status, 1);
  assert.match(unguarded.detail, /unguarded alias cycle through Box: a recursive alias must reach itself through an object, array, tuple or function type/);
}
{
  // `new` at a variadic construct signature reads a spread where it is
  // written, its copy taken before a later actual runs; a class whose code
  // binds positions the rest may leave out is refused at the signature, as
  // Node shows it throwing there.
  assert.equal(runExample("constructor-rest-spread", "order"), 218);
  assert.equal(runExample("constructor-rest-spread", "run"), 14);
  assert.throws(() => runExample("invalid-constructor-rest-class", "made"), /reading 'toFixed'/);
}
{
  // A packed class binder: `run` spreads the stored array into the
  // callback; a shorter array stored by `set` leaves the callback's
  // parameter `undefined`, as Node shows it throwing.
  assert.equal(runExample("class-rest-binder", "kept"), 52);
  assert.equal(runExample("class-rest-binder", "paired"), 7);
  assert.throws(() => runExample("invalid-class-rest-binder-set", "lost"), /reading 'toFixed'/);
}
{
  // An array literal's spread is copied before a later element that runs
  // code, as JavaScript reads it there; a spread operand claimed at other
  // than an array is refused where the elements are produced and checked.
  const good = run("array-literal-spread");
  assert.equal(runExample("array-literal-spread", "snapshot()"), 22);
  const source = readFileSync(join(good, "source.ts"), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "appended"), "appended function");
  const start = source.indexOf("[...xs, x]") + "[...".length;
  const operand = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 2), "spread operand claim");
  const number = claims.types.findIndex(r => Array.isArray(r) && r.length === 1 && r[0] === "num");
  assert(number >= 0);
  operand.type = [number];
  const forged = writeClaims(good, "array-spread-number", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(verifier, [mode, join(good, "fragment.json"), forged,
      join(good, "source.ts"), join(good, mode === "--produce-source-claims"
        ? "array-spread-forged-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
  }
}
{
  const good = run("constructor-tuple-spread");
  assert.equal(runExample("constructor-tuple-spread", "snapshot()"), 12);
  const source = readFileSync(join(good, "source.ts"), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "snapshot"), "snapshot function");
  const flow = decodeFlowDocument(JSON.parse(readFileSync(join(good, "flow.json"), "utf8")));
  const owner = must(flow.find(f => JSON.stringify(f.owner) === JSON.stringify(fn.namePos)), "snapshot flow");
  const statement = must(owner.nodes.find(n => n.action.kind === "declaration" && n.action.name === "result"), "constructor binding");
  const operations = (p: ExecutionPlan): ExecutionOperation[] => {
    switch (p.kind) {
      case "atom": return [p.operation];
      case "observe": return operations(p.evaluate);
      case "sequence": return [...operations(p.evaluate), ...operations(p.next)];
      case "choose": throw Error("the constructor-order fixture has no conditional evaluation");
    }
  };
  assert(statement.action.kind === "declaration");
  const initializer = statement.action.initializer;
  const execution = must(statement.executions.find(e => JSON.stringify(e.source) === JSON.stringify(initializer)), "constructor execution");
  const ops = operations(execution.plan);
  const events = ops.filter(o => o.kind === "snapshotSpread" ||
    (o.kind === "evaluate" && o.effect.kind === "havoc"));
  assert.deepEqual(events.map(o => o.kind === "snapshotSpread" ? "snapshot" : source.slice(...o.source)),
    ["(choose(xs))", "snapshot", "replace(xs)", "new (choose(xs))(...xs, replace(xs))"]);
  const snapshot = must(ops.find(o => o.kind === "snapshotSpread"), "spread snapshot");
  const number = claims.types.findIndex(r => Array.isArray(r) && r.length === 1 && r[0] === "num");
  assert(number >= 0);
  const read = must(fn.expressions.find(e => JSON.stringify(e.pos) === JSON.stringify(snapshot.source)), "spread operand claim");
  read.type = [number];
  const forged = writeClaims(good, "constructor-spread-number", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(verifier, [mode, join(good, "fragment.json"), forged,
      join(good, "source.ts"), join(good, mode === "--produce-source-claims"
        ? "constructor-forged-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.match(result.stdout + result.stderr, /constructor spread needs a tuple contract/);
  }
}
{
  const good = run("generic-prototype-instanceof");
  const ast: Ast = JSON.parse(readFileSync(join(good, "fragment.json"), "utf8"));
  const statement = ast.functions.find((f) => f.name === "typedIdentity")?.body[0];
  assert(statement?.k === "if" && statement.cond.k === "instanceTest");
  const pos = statement.cond.proto.pos;
  for (const variant of ["number", "unbound"]) {
    const claims = readClaims(good);
    const fn = must(claims.functions.find((f) => f.name === "typedIdentity"), "consumer");
    const read = must(fn.expressions.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]), "prototype read");
    const number = claims.types.findIndex((r) => Array.isArray(r) && r.length === 1 && r[0] === "num");
    assert(number >= 0);
    read.type = variant === "number" ? [number] : [{ binder: "UnboundPrototypeParameter" }];
    const forged = writeClaims(good, `prototype-${variant}`, claims);
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const result = spawnSync(verifier, [mode, join(good, "fragment.json"), forged,
        join(good, "source.ts"), join(good, mode === "--produce-source-claims"
          ? `prototype-${variant}-evidence.json` : "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : [])],
        { encoding: "utf8", timeout: 30_000 });
      assert.ifError(result.error);
      assert.equal(result.status, 1, result.stdout + result.stderr);
      assert.match(result.stdout + result.stderr, variant === "unbound"
        ? /a label names a binder no unit or closure reads/
        : /evidence search failed|source evidence does not justify/);
    }
  }
  process.stdout.write("prototype contracts: invented read types and unbound parameters refused in both modes\n");
}
{
  // A class's generic method, a closure the prototype holds, covers the
  // instance type's member up to renaming the member's binders to the
  // closure's: the renamed signatures must still follow from the closure's.
  // The class's declaration tampered to promise a number where the closure
  // returns its binder is refused at the construct code's return, where the
  // fresh instance meets the instance type; the untampered one is derived there.
  // `make` alone is kept, so the construct code is the first obligation.
  const classGeneric = run("class-generic-method");
  const source = readFileSync(join(classGeneric, "source.ts"), "utf8");
  const claims = readClaims(classGeneric);
  claims.functions = claims.functions.filter((f) => f.name === "make");
  const makeClaims = writeClaims(classGeneric, "make-claims", claims);
  const fragment: unknown = JSON.parse(readFileSync(join(classGeneric, "fragment.json"), "utf8"));
  assert.ok(fragment && typeof fragment === "object" && "functions" in fragment &&
    Array.isArray(fragment.functions));
  fragment.functions = fragment.functions.filter((f: unknown) =>
    f && typeof f === "object" && "name" in f && f.name === "make");
  const kept = JSON.stringify(fragment);
  const at = source.indexOf("pick<V>(a: V): V") + "pick<V>(a: V): ".length;
  const declared = `"result":{"k":"binder","name":"V","span":[${at},${at + 1}]}`;
  assert.ok(kept.includes(declared), "pick's declared result");
  const search = (name: string, text: string) => {
    const ast = join(classGeneric, `${name}.json`);
    writeFileSync(ast, text);
    return produceWith(classGeneric, makeClaims, name, ast);
  };
  const derived = search("make-only", kept);
  assert.equal(derived.status, 0, derived.stdout + derived.stderr);
  const refused = search("forged-member-result",
    kept.replace(declared, '"result":{"k":"atom","name":"number","span":[0,0]}'));
  assert.equal(refused.status, 1, refused.stdout + refused.stderr);
  const ctor = source.indexOf("class Helper") + "class ".length;
  assert.ok((refused.stdout + refused.stderr).includes(
    `source expression obligation at [${ctor},${ctor + "Helper".length}): evidence search failed: no derivation of its return-contract claim`),
    refused.stdout + refused.stderr);
  process.stdout.write("forged declarations: an erased contract, binder roles, an unguarded alias and an uncovered member refused by the verifier\n");
}

{
  const good = run("values");
  const original = readClaims(good);
  for (const [name, mutate] of [
    ["fingerprint", (c: SourceClaims) => { c.sourceSha256 = "0".repeat(64); }],
    ["missing-function", (c: SourceClaims) => { c.functions.pop(); }],
  ] as const) {
    const c = structuredClone(original);
    mutate(c);
    invoke(writeClaims(good, name, c), join(good, "evidence.json"), good);
    process.stdout.write(`tampered ${name}: refused\n`);
  }
  // A missing claim is a located refusal, not prose disguised as a failed
  // judgment. The closed failure sum makes this branch mandatory at the
  // Lean boundary, and the reader must preserve the distinction.
  const generic = run("generic-inferred");
  const claims = readClaims(generic);
  const fn = must(claims.functions.find((f) => f.name === "inferred"), "inferred");
  fn.expressions.pop();
  const refusal = readDiagnostic(invoke(writeClaims(generic, "missing-generic-expression", claims),
    join(generic, "evidence.json"), generic));
  assert(refusal?.kind === "source-refusal");
  assert.deepEqual(refusal.sourceMap.pos, fn.namePos);
  assert(!("judgment" in refusal));
  // The claims name declarations by their position in the fragment's
  // document: under another import closure they are other types, which the
  // evidence does not justify.
  const fragment: unknown = JSON.parse(readFileSync(join(good, "fragment.json"), "utf8"));
  const json: unknown = JSON.parse(readFileSync(join(run("collections-json-uninherited-key"), "fragment.json"), "utf8"));
  assert.ok(fragment && typeof fragment === "object" && json && typeof json === "object" && "declarations" in json);
  const forgedImport = join(good, "forged-import.json");
  writeFileSync(forgedImport, JSON.stringify({ ...fragment, declarations: json.declarations }));
  assert.match(invoke(join(good, "claims.json"), join(good, "evidence.json"), good, forgedImport),
    /source evidence does not justify/);
  process.stdout.write("forged import closure: refused\n");
}
{
  // Each label tree has one spelling and names a declaration of the fragment's
  // document; a binder is a label, never a row the producer writes.
  const recursiveJson = run("collections-json-uninherited-key");
  const path = join(recursiveJson, "claims.json");
  const claims = readClaims(recursiveJson);
  const nullary = Number(must(/\{"decl":(\d+)\}/.exec(readFileSync(path, "utf8")),
    "a nullary declaration's label")[1]);
  const param = must(claims.functions[0]?.params[0], "a parameter's claim");
  const forge = (name: string, type: unknown, row: unknown[] = []) => {
    const forged = join(recursiveJson, `forged-label-${name}.json`);
    writeFileSync(forged, JSON.stringify({ ...claims, types: [...claims.types, ...row] },
      (_key, value: unknown) => value === param.type ? type : value));
    return invoke(forged, join(recursiveJson, "evidence.json"), recursiveJson);
  };
  for (const [name, type, refusal] of [
    ["unknown-field", [{ decl: nullary, span: [0, 0] }], /unexpected fields/],
    ["nullary-arguments", [{ decl: nullary, args: [] }], /a nullary declaration's label leaves its arguments out/],
    ["missing-declaration", [{ decl: 1000 }], /a declaration's label names no declaration/],
    ["missing-arguments", [{ decl: nullary, args: [[3]] }], /one argument per parameter/],
    ["order", [{ binder: "T" }, 3], /canonical order/],
    ["one-part-meet", [{ meet: [[3]] }], /at least two parts/],
  ] as const)
    assert.match(forge(name, type), refusal, name);
  assert.match(forge("parameter-row", [claims.types.length],
    [{ param: claims.types.length, name: "T", kind: "value" }]),
    /a producer's row is a clause row or a scheme row/);
  process.stdout.write("label trees other than the one spelling, and a binder as a producer row: refused\n");
}

{
  // The named view remains part of a mixed dictionary's source contract: an
  // index-only replacement must not certify a function annotated with both.
  const indexed = run("index-signature-uninherited-key");
  const claims = readClaims(indexed);
  const mixed = must(claims.types.find((row) =>
    row.length === 1 && typeof row[0] === "object" && "dict" in row[0] &&
    row[0].dict.views.some(([name]) => name === "ready")), "the mixed dictionary row");
  const clause = mixed[0];
  assert(typeof clause === "object" && "dict" in clause);
  clause.dict.views = [];
  assert.match(invoke(writeClaims(indexed, "forged-missing-named-view", claims), join(indexed, "evidence.json"), indexed),
    /claimed parameter type differs from the source annotation/);
}
{
  // A `keyof` with a unique symbol names that one symbol: claims naming
  // another symbol, or every symbol, in its place differ from the annotation
  // the verifier reads itself.
  const keyed = run("keyof-unique-symbol");
  const forgeries: [string, (id: number) => Row[number]][] = [
    ["other-unique-symbol", (id) => ({ symbolLit: { id: id + 1 } })],
    ["every-symbol", () => "symbol"],
  ];
  for (const [name, clause] of forgeries) {
    const claims = readClaims(keyed);
    const rows = claims.types.filter((row) => row.length === 1 && typeof row[0] === "object" && "symbolLit" in row[0]);
    assert.ok(rows.length > 0, "the claims name a unique symbol");
    for (const row of rows) {
      const [only] = row;
      if (typeof only === "object" && "symbolLit" in only) row[0] = clause(only.symbolLit.id);
    }
    assert.match(invoke(writeClaims(keyed, `forged-${name}`, claims), join(keyed, "evidence.json"), keyed),
      /claimed (return|parameter) type differs from the source annotation/, name);
  }
  process.stdout.write("a keyof's unique symbol claimed as another symbol or every symbol: refused\n");
}
// A method or constructor claim is compared with its annotation by meaning, so
// another row for Values<number> is admitted; a domain wider than the
// annotation, here one that also admits undefined, is still refused.
for (const [artifacts, arity, refusal] of [
  [run("collections-mapper-signature"), 2, /closure signature claim is outside the source annotation/],
  [run("collections-constructor-field"), 1, /construct signature claim is outside the source annotation/],
] as const) {
  const claims = readClaims(artifacts);
  // mapEntry's arrow, or AddIndex's construct signature: its last parameter.
  const domains = claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause !== "object" ? [] :
    "arrs" in clause ? clause.arrs.arrows.map((s) => s.arguments) :
    "ctors" in clause ? clause.ctors.signatures.map(([params]) => params) : []));
  const params = must(domains.find((ps) => ps.length === arity), "the claimed signature");
  must(params.at(-1), "a claimed parameter").unshift(3);
  assert.match(invoke(writeClaims(artifacts, "forged-wider-domain", claims), join(artifacts, "evidence.json"), artifacts), refusal);
}
{
  // A closure is created at a variadic signature only when the signature's
  // fixed parameters cover the ones its code binds: `named` binds one, so a
  // claim offering it `(...rest: unknown[]) => void` is refused where it is
  // created, not taken from the producer on trust.
  const variadicOffer = run("variadic-offer-sync");
  const claims = readClaims(variadicOffer);
  const offered = must(claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause === "object" && "arrs" in clause && clause.arrs.arrows.length > 0
      ? clause.arrs.variadic ?? [] : []))
    .find((s) => s.arguments[0].length === 1), "the variadic signature `named` is offered");
  offered.arguments[0] = [];
  assert.match(invoke(writeClaims(variadicOffer, "forged-variadic-offer", claims), join(variadicOffer, "evidence.json"), variadicOffer),
    /closure signature claim is outside the source annotation/);
}
{
  // The unannotated closure's body returns a number. Its claimed null result
  // is checked by the body's return obligation.
  const localClosure = run("closure-result-contract");
  const claims = readClaims(localClosure);
  const source = readFileSync(join(localClosure, "source.ts"), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "minus"), "minus's claims");
  const closure = must(fn.expressions.find((e) => e.pos[0] === source.indexOf("(p: number")),
    "the unannotated closure's expression claim");
  assert.ok(Array.isArray(closure.type));
  assert.equal(closure.type.length, 1);
  const label = closure.type[0];
  assert.ok(typeof label === "number");
  const originalType = structuredClone(closure.type);
  // The closure value uses a private row; reduce retains its declared instance.
  const row = structuredClone(must(claims.types[label], "the closure's type row"));
  const own = must(row.flatMap((clause) =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])
    .find((s) => s.arguments.length === 2), "the closure's own arrow");
  own.result = [0];
  const forgedType = [claims.types.push(row) - 1];
  for (const expression of fn.expressions) {
    if (JSON.stringify(expression.type) === JSON.stringify(originalType)) expression.type = forgedType;
  }
  for (const entry of fn.entries) {
    for (const binding of entry.bindings) {
      if (binding.name === "acc") binding.type = forgedType;
    }
  }
  const body = source.indexOf("p !== null");
  refusedAt(localClosure, writeClaims(localClosure, "forged-closure-result", claims), "forged-closure-result",
    `source expression obligation at [${body},`);
  process.stdout.write("claims wider than their annotations: refused\n");
}


{
  // Point identities bind claims to executions of the shared graph. Source
  // provenance alone cannot authorize a claim at another graph point.
  const artifacts = run("values");
  const original = readClaims(artifacts);
  const first = must(original.functions[0]?.expressions[0], "a graph-point claim");
  const foreign = must(original.functions[1]?.expressions[0], "another function's point");
  for (const [name, replacement] of [
    ["unknown-point", first.point.replace(/:[0-9]+$/, ":999999999")],
    ["foreign-point", foreign.point],
  ]) {
    const claims = readClaims(artifacts);
    must(claims.functions[0]?.expressions[0], "the graph-point claim").point = replacement;
    const forged = writeClaims(artifacts, name, claims);
    const searched = produceWith(artifacts, forged, name);
    assert.notEqual(searched.status, 0, `${name}: forged graph point accepted by search`);
    assert.match(searched.stdout + searched.stderr, /expression claim names a foreign or missing execution point/);
    assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /expression claim names a foreign or missing execution point/);
  }
  const duplicate = readClaims(artifacts);
  const fn = must(duplicate.functions[0], "the first function");
  fn.expressions.push(structuredClone(must(fn.expressions[0], "the duplicated point")));
  const forged = writeClaims(artifacts, "duplicate-point", duplicate);
  const duplicated = produceWith(artifacts, forged, "duplicate-point");
  assert.notEqual(duplicated.status, 0);
  assert.match(duplicated.stdout + duplicated.stderr, /invalid source claims: duplicate identity/);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /invalid source claims: duplicate identity/);
  // A lifetime contract is checked independently of its point observations.
  const retyped = readClaims(artifacts);
  const mutable = must(retyped.functions.find((f) => f.name === "mutable"), "mutable");
  must(mutable.contracts.find((c) => c.name === "value"), "value's storage contract").type = [1];
  const wrongContract = writeClaims(artifacts, "forged-storage-contract", retyped);
  assert.notEqual(produceWith(artifacts, wrongContract, "forged-storage-contract").status, 0);
  assert.match(invoke(wrongContract, join(artifacts, "evidence.json"), artifacts), /contract|claim|evidence/);
}

{
  // A contract proposed from an evolving binding's uses is a claim: forged
  // to `null` alone, the write of a list cell into the binding is refused.
  const artifacts = run("evolving-use-contract");
  const claims = readClaims(artifacts);
  const reverse = must(claims.functions.find((f) => f.name === "reverse"), "reverse");
  const contract = must(reverse.contracts.find((c) => c.name === "result"), "result's storage contract");
  const nul = claims.types.findIndex((t) => JSON.stringify(t) === JSON.stringify(["nul"]));
  assert.ok(nul >= 0, "a null type label");
  contract.type = [nul];
  const forged = writeClaims(artifacts, "forged-use-contract", claims);
  assert.notEqual(produceWith(artifacts, forged, "forged-use-contract").status, 0);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /contract|claim|evidence/);
  process.stdout.write("evolving use contract: a forged contract refused at the write\n");
}


{
  // A deferred closure body owns execution points separate from creation.
  const artifacts = run("closure-graph-try");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const fn = must(claims.functions[0], "guarded");
  const creation = must(fn.expressions.find((e) => e.pos[0] === source.indexOf("(): number =>")), "closure creation");
  const at = source.indexOf("return g();") + "return ".length;
  must(fn.expressions.find((e) => e.pos[0] === at && e.pos[1] === at + 3), "deferred call").point = creation.point;
  const forged = writeClaims(artifacts, "deferred-at-creation", claims);
  const deferred = produceWith(artifacts, forged, "deferred-at-creation");
  assert.notEqual(deferred.status, 0);
  assert.match(deferred.stdout + deferred.stderr, /expression claim at .*outside its execution point/);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /expression claim at .*outside its execution point/);
}
{
  // A copied finalizer's source site belongs to each actual finalizer action.
  const artifacts = run("try-finally-jump");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "breakThroughFinally"), "breakThroughFinally");
  const at = source.indexOf("count = count * 2");
  const copies = fn.expressions.filter((e) => e.pos[0] === at && e.pos[1] === at + "count = count * 2".length);
  assert.ok(new Set(copies.map((e) => e.point)).size > 1, "distinct finalizer executions");
  const unrelated = must(fn.expressions.find((e) => e.pos[1] <= at && !copies.some((c) => c.point === e.point)), "another execution point");
  must(copies[0], "the copied finalizer claim").point = unrelated.point;
  const forged = writeClaims(artifacts, "finalizer-at-other-point", claims);
  const finalizer = produceWith(artifacts, forged, "finalizer-at-other-point");
  assert.notEqual(finalizer.status, 0);
  assert.match(finalizer.stdout + finalizer.stderr, /expression claim at .*outside its execution point/);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /expression claim at .*outside its execution point/);
}

{
  // A condition of a Boolean literal type takes one arm (`ifKnown`): claimed at
  // that arm alone, `ready || zs[0]` is `true`, as Node computes. The same claim
  // is refused at that expression where the condition is a binding a closure
  // resets before the arm is chosen, and Node finds `undefined` there.
  for (const [file, call, expected] of [
    ["known-condition", "known([])", true],
    ["invalid-known-condition", "stale([])", undefined],
  ] as const) {
    const artifacts = run(file);
    const source = readFileSync(join(artifacts, "source.ts"), "utf8");
    const claims = readClaims(artifacts);
    const condition = "ready || zs[0]";
    const at = source.lastIndexOf(condition);
    const claim = must(claims.functions.flatMap((f) => f.expressions)
      .find((e) => e.pos[0] === at && e.pos[1] === at + condition.length), "the condition's claim");
    claim.type = [rowOf(claims, { boolLit: { value: true } })];
    const forged = writeClaims(artifacts, "forged-known-arm", claims);
    if (expected) {
      const searched = produceWith(artifacts, forged, "forged-known-arm");
      assert.equal(searched.status, 0, searched.stdout + searched.stderr);
    } else refusedAt(artifacts, forged, "forged-known-arm", `source expression obligation at [${at},${at + condition.length})`);
    assert.equal(runExample(file, call), expected);
  }
}
{
  // On `cell-union-capture`, whose captured cell is of a union of a
  // `null | boolean` arm and a `null` arm, a contents observation every arm
  // implies holds where the closure reads the cell, and a null-only one is
  // refused there, as one arm admits later Boolean writes. A statement entry's
  // null-only observation holds after the closure writes `null` into the cell,
  // and not where nothing wrote it; an entry narrowing the cell to its null arm
  // is refused at its entry, though its observation holds.
  const cellUnion = run("cell-union-capture");
  const source = readFileSync(join(cellUnion, "source.ts"), "utf8");
  const within = (fn: string, text: string): number => {
    const start = source.indexOf(`function ${fn}(`);
    const at = source.indexOf(text, start);
    assert.ok(start >= 0 && at > start && at < source.indexOf("\n}", start), `${text} in ${fn}`);
    return at;
  };
  const labels = (claims: SourceClaims) => ({
    nul: rowOf(claims, "nul"),
    every: [rowOf(claims, "nul"), rowOf(claims, { boolLit: { value: true } }), rowOf(claims, { boolLit: { value: false } })],
    nullArm: rowOf(claims, { refs: { first: [["value", [rowOf(claims, "nul")]]], rest: [], views: [] } }),
  });
  /** The claims with the captured cell observed at `pick`'s labels, at the
   * expression or statement entry starting at `at`. */
  const observed = (fn: string, at: number, name: string,
      pick: (l: ReturnType<typeof labels>) => number[], site: "expression" | "entry", narrowed = false): string => {
    const claims = readClaims(cellUnion);
    const l = labels(claims);
    const f = must(claims.functions.find((g) => g.name === fn), fn);
    const points = site === "expression"
      ? f.expressions.filter((e) => e.pos[0] === at && e.pos[1] === at + "cell".length)
      : f.entries.filter((e) => e.start === at).flatMap((e) => e.bindings.filter((b) => b.name === "cell"));
    assert.equal(points.length, 1, `one point observed in ${fn} at ${at}`);
    for (const p of points) {
      p.current = [["value", pick(l)]];
      if (narrowed) p.type = [l.nullArm];
    }
    return writeClaims(cellUnion, name, claims);
  };
  const edge = (span: [number, number]) => `source incoming edge obligation at [${span[0]},${span[1]})`;
  const read = within("readLater", "=> cell.value") + "=> ".length;
  assert.equal(produceWith(cellUnion, observed("readLater", read, "observed-every", (l) => l.every, "expression"), "observed-every").status, 0);
  refusedAt(cellUnion, observed("readLater", read, "observed-null", (l) => [l.nul], "expression"), "observed-null", edge([read, read + 4]));
  const written = within("writeThenRead", "return cell.value;");
  assert.equal(produceWith(cellUnion, observed("writeThenRead", written, "entry-written", (l) => [l.nul], "entry"),
    "entry-written").status, 0);
  const unwritten = within("readBlock", "return cell.value;");
  refusedAt(cellUnion, observed("readBlock", unwritten, "entry-unwritten", (l) => [l.nul], "entry"), "entry-unwritten",
    edge([unwritten, unwritten + "return cell.value;".length]));
  refusedAt(cellUnion, observed("writeThenRead", written, "entry-null-arm", (l) => [l.nul], "entry", true), "entry-null-arm",
    edge([written, written + "return cell.value;".length]));
}
{
  // The result of a call through a captured union of functions is not narrowed
  // to one alternative's: claimed `true`, the call is refused where it is.
  const callableUnion = run("callable-union-capture");
  const source = readFileSync(join(callableUnion, "source.ts"), "utf8");
  const claims = readClaims(callableUnion);
  const at = source.indexOf("f(unit)");
  must(claims.functions.flatMap((f) => f.expressions).find((e) => e.pos[0] === at && e.pos[1] === at + 7),
    "the call's claim").type = [rowOf(claims, { boolLit: { value: true } })];
  refusedAt(callableUnion, writeClaims(callableUnion, "forged-one-arm", claims), "forged-one-arm",
    `source expression obligation at [${at},${at + 7})`);
}
{
  // A bound method's variadic signature is covered by the member's when the
  // claimed rest is within the member's (`CoveredRestUsing`): `merge`'s rest,
  // the producer's own row for `EagerCollection<string, number>[]`, admits the
  // declared rest's lists. Widened to admit strings too, the claim is refused
  // at the bound member.
  const collections = run("collections-collections");
  const claims = readClaims(collections);
  const rest = must(claims.types.flatMap((row) => row.flatMap((clause) =>
    typeof clause === "object" && "pack" in clause ? [clause.pack.first] : []))
    .find((t) => t.rest !== null), "merge's claimed rest").rest;
  must(rest, "the rest's labels").unshift(4);
  const member = readFileSync(join(collections, "source.ts"), "utf8").indexOf("cs.input1.merge");
  refusedAt(collections, writeClaims(collections, "forged-wider-rest", claims), "forged-wider-rest",
    `source expression obligation at [${member},${member + "cs.input1.merge".length})`);
}
{
  // Explicit type arguments, written as another type than the one the claimed
  // instance fits: on a method call, `reduce<number | null>` written as
  // `reduce<number | null | string>`, and on a plain call, `same<number |
  // boolean>` written as `same<number | boolean | string>`. The claims are
  // unchanged, so each call's instance fits its actuals but is not the one the
  // call states.
  const forgeTypeArgument = (artifacts: string, kind: "invoke" | "apply"): string => {
    type TypeArgument = { parts: unknown[]; span: unknown };
    const isTypeArgument = (a: unknown): a is TypeArgument =>
      !!a && typeof a === "object" && "parts" in a && Array.isArray(a.parts) && "span" in a;
    const ast: unknown = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
    // Each call's type arguments, as the Fragment holds them: the forgery edits them there.
    const calls: TypeArgument[][] = [];
    const visit = (j: unknown): void => {
      if (Array.isArray(j)) j.forEach(visit);
      else if (j && typeof j === "object") {
        if ("k" in j && j.k === kind && "typeArgs" in j && Array.isArray(j.typeArgs) && j.typeArgs.every(isTypeArgument))
          calls.push(j.typeArgs);
        Object.values(j).forEach(visit);
      }
    };
    visit(ast);
    const [typeArg] = must(calls[0], "the call's type arguments");
    must(typeArg, "the type argument").parts.push({ k: "atom", name: "string", span: typeArg.span });
    const forgedAst = join(artifacts, "forged-type-argument.json");
    writeFileSync(forgedAst, JSON.stringify(ast));
    return forgedAst;
  };
  for (const [artifacts, kind] of [[run("closure-result-contract"), "invoke"], [run("explicit-type-arguments"), "apply"]] as const)
    assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts,
      forgeTypeArgument(artifacts, kind)),
      /the call's instance is not the one its explicit type arguments state/);
}
{
  // A writable index is never met through an own-key bound: a callee holding
  // the object as a writable dictionary may add a key the bound says is absent.
  // Claims forged to state one, the literal's exact keys (none) or the rest's
  // lacking the pattern's key `x`, are refused at allocation or the call handing
  // the object to the callee. Run as JavaScript with a callee that stores `x`, each function
  // returns the string stored, where its result claims `number | undefined`.
  for (const [file, name, call, clause] of [
    ["invalid-writable-dictionary-exact-keys", "o", "exact((d) => { d.x = 's'; })",
      (_str: number): Row[number] => ({ refs: { first: [], rest: [], views: [],
        bounds: [{ among: true, keys: [] }] } })],
    ["invalid-writable-dictionary-rest-keys", "r", "rest((d) => { d.x = 's'; }, {})",
      (str: number): Row[number] => ({ dict: { first: [], rest: [], views: [],
        indexes: [["strings", [str]]], cells: [["strings", [str]]],
        bounds: [{ among: false, keys: ["x", "[[proto]]"] }] } })],
  ] as const) {
    const artifacts = run(file);
    const source = readFileSync(join(artifacts, "source.ts"), "utf8");
    const claims = readClaims(artifacts);
    const str = claims.types.findIndex((row) => row.length === 1 && row[0] === "str");
    assert.ok(str >= 0, "the string row");
    const label = claims.types.push([clause(str)]) - 1;
    const fn = must(claims.functions[0], "the function's claims");
    for (const entry of fn.entries)
      for (const b of entry.bindings) if (b.name === name) b.type = [label];
    // The object's own sites: its allocation (`{}`, `...r`) and every read of it.
    for (const e of fn.expressions)
      if ([name, "{}", `...${name}`].includes(source.slice(e.pos[0], e.pos[1]))) e.type = [label];
    const searched = produceWith(artifacts, writeClaims(artifacts, "forged-own-key-bound", claims), "forged-own-key-bound");
    const detail = searched.stdout + searched.stderr;
    assert.equal(searched.status, 1, detail);
    const at = /source expression obligation at \[(\d+),(\d+)\)/.exec(detail);
    if (file === "invalid-writable-dictionary-rest-keys") {
      const rest = source.indexOf("...r");
      assert.ok(at, detail);
      assert.deepEqual([Number(at[1]), Number(at[2])], [rest, rest + 4]);
      const diagnostic = readDiagnostic(detail);
      assert.ok(diagnostic?.kind === "node-typing");
      assert.equal(diagnostic.source.sourceMap?.role, "pattern-read");
    } else {
      const site = source.indexOf(`add(${name})`);
      assert.ok(at && Number(at[1]) >= site && Number(at[2]) <= site + `add(${name})`.length, detail);
    }
    assert.equal(runExample(file, call), "s");
  }
}
{
  // A generic body is a graph request over its binders' parameter rows. Reusing
  // valid evidence must not let an inferred local trust a forged point type,
  // at its initializer's expression or at its entry binding.
  const generic = run("generic-inferred");
  for (const site of ["initializer", "binding"] as const) {
    const claims = readClaims(generic);
    const fn = must(claims.functions.find((f) => f.name === "inferred"), "inferred");
    if (site === "initializer") must(fn.expressions[0], "the initializer's claim").type = [1, 2];
    else must(fn.entries.flatMap((e) => e.bindings).find((b) => b.name === "saved"), "saved").type = [1, 2];
    assert.match(invoke(writeClaims(generic, `forged-${site}`, claims), join(generic, "evidence.json"), generic),
      /source evidence does not justify the extracted program and exact claims/);
  }
}
{
  // A captured cell keeps the contract its declaration states. Retyping it in the
  // entry claim changes what the closure's code, checked once at its scheme, is
  // entered with, so the check refuses: a capture is never retyped per call.
  const captured = run("generic-captured-store");
  const claims = readClaims(captured);
  const fn = must(claims.functions[0], "the containing function");
  const declaration = must(fn.entries.find((e) => e.bindings.some((b) => b.name === "store") &&
    !e.bindings.some((b) => b.name === "read")), "the entry at the closure's declaration");
  must(declaration.bindings.find((b) => b.name === "store"), "store").type = [1, 2];
  assert.match(invoke(writeClaims(captured, "forged-capture", claims), join(captured, "evidence.json"), captured),
    /does not justify|evidence search failed/);
}
{
  // A module function is reached at its own annotated signature, which Lean
  // reads from the source; a producer cannot retype the callee.
  const moduleFunctions = run("module-functions");
  const claims = readClaims(moduleFunctions);
  const source = readFileSync(join(moduleFunctions, "source.ts"), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "twice"), "twice");
  const callee = source.indexOf("id(id(x))");
  const site = must(fn.expressions.find((e) => e.pos[0] === callee && e.pos[1] === callee + 2), "the outer callee's claim");
  site.type = must(fn.expressions.find((e) => e.pos[0] === source.indexOf("x))", callee)), "the argument's claim").type;
  invoke(writeClaims(moduleFunctions, "forged-callee", claims), join(moduleFunctions, "evidence.json"), moduleFunctions);
}
{
  // Only a module function without a rest parameter has its signature
  // extended by a rest of `unknown` in its slot: claiming one with a rest at
  // the longer signature its use expects is refused where it is read.
  const collects = run("invalid-named-function-arity");
  const claims = readClaims(collects);
  const source = readFileSync(join(collects, "source.ts"), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "widen"), "widen");
  const at = source.indexOf("collects;");
  must(fn.expressions.find((e) => e.pos[0] === at && e.pos[1] === at + "collects".length), "the read's claim").type = fn.result;
  refusedAt(collects, writeClaims(collects, "forged-collects-longer", claims), "forged-collects-longer",
    `source expression obligation at [${at},${at + "collects".length})`);
}
{
  // The initialization unit's claims are checked like a function's: claiming
  // the constant's initializer at another type is refused.
  const moduleInit = run("module-init");
  const claims = readClaims(moduleInit);
  const source = readFileSync(join(moduleInit, "source.ts"), "utf8");
  const init = must(claims.init, "the initialization unit's claims");
  must(init.expressions.find((e) => e.pos[0] === source.indexOf("true;")), "the initializer's claim").type = [0];
  invoke(writeClaims(moduleInit, "forged-initializer", claims), join(moduleInit, "evidence.json"), moduleInit);
}
{
  // A call's substitution is the elimination it proposes, so evidence produced
  // for the checked substitutions cannot certify a different one: at a plain
  // call (its type argument, and its binder's name), at a call of a generic
  // module function, and at a call through a callback.
  const twoCalls = run("generic-two-calls");
  for (const [name, mutate] of [
    ["substitution", (s: NonNullable<SourceClaims["functions"][number]["expressions"][number]["instantiate"]>) => {
      must(s[0], "the inferred type argument").type = [1, 2];
    }],
    ["substitution-domain", (s: NonNullable<SourceClaims["functions"][number]["expressions"][number]["instantiate"]>) => {
      must(s[0], "the inferred type argument").name = "U";
    }],
  ] as const) {
    const claims = readClaims(twoCalls);
    const sites = must(claims.functions[0], "the containing function").expressions.filter((e) => e.instantiate);
    assert.equal(sites.length, 2, "both eliminations must carry a substitution");
    const source = readFileSync(join(twoCalls, "source.ts"), "utf8");
    const countCall = must(sites.find((e) => source.slice(e.pos[0], e.pos[1]) === "id(count)"), "the numeric call");
    mutate(must(countCall.instantiate, "the numeric substitution"));
    invoke(writeClaims(twoCalls, `forged-${name}`, claims), join(twoCalls, "evidence.json"), twoCalls);
  }
  const genericModule = run("generic-module-calls");
  const moduleClaims = readClaims(genericModule);
  const both = must(moduleClaims.functions.find((f) => f.name === "both"), "both");
  const call = must(both.expressions.find((e) => e.instantiate?.length)?.instantiate, "an instantiated call");
  must(call[0], "its type argument").type = [0];
  invoke(writeClaims(genericModule, "forged-instance", moduleClaims), join(genericModule, "evidence.json"), genericModule);
  const callback = run("generic-callback");
  const callbackClaims = readClaims(callback);
  const through = must(callbackClaims.functions.find((f) => f.name === "throughCallback"), "throughCallback");
  const site = must(through.expressions.find((e) => e.instantiate?.some((i) => Array.isArray(i.type) && i.type.length === 2))
    ?.instantiate, "the call instantiated at boolean");
  must(site[0], "the callback substitution").type = [4];
  invoke(writeClaims(callback, "forged-callback-instance", callbackClaims), join(callback, "evidence.json"), callback);
}
{
  // A graph certificate for the checked Boolean instance cannot validate a
  // different quantified contract. The scheme itself is independently consumed.
  const genericClosure = run("generic-closure");
  const claims = readClaims(genericClosure);
  const schemePoint = must(claims.functions[0], "the closure's function").expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type);
  assert.ok(schemePoint && !Array.isArray(schemePoint.type) && "scheme" in schemePoint.type);
  schemePoint.type.scheme.result = [1, 2];
  invoke(writeClaims(genericClosure, "forged-scheme", claims), join(genericClosure, "evidence.json"), genericClosure);
}
{
  // A nested closure's claim is checked at the scheme's binder: a ground
  // `() => boolean` claim fits every observed call and is still refused, since
  // the body returns a `T`. And a callable over the binder is meaningful only
  // inside its closure: the same claim placed on an expression outside it names
  // a binder not in scope there.
  const returned = run("generic-returned");
  const returnedClaims = readClaims(returned);
  const fn = must(returnedClaims.functions[0], "the containing function");
  const nested = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length === 0);
  assert.ok(nested && !Array.isArray(nested.type) && "scheme" in nested.type);
  const outer = fn.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type && e.type.scheme.typeParams.length > 0);
  assert.ok(outer && !Array.isArray(outer.type) && "scheme" in outer.type);
  const grounded = structuredClone(returnedClaims);
  const g = must(grounded.functions[0], "the containing function").expressions.find((e) => e.pos[0] === nested.pos[0] && e.pos[1] === nested.pos[1]);
  assert.ok(g && !Array.isArray(g.type) && "scheme" in g.type);
  g.type.scheme.result = [1, 2];
  // The body `value` is a `T`, and the return-contract obligation at it asks
  // for a boolean: no derivation exists.
  const body = readFileSync(join(returned, "source.ts"), "utf8").indexOf("value;");
  refusedAt(returned, writeClaims(returned, "forged-nested-claim", grounded), "forged-nested",
    `source expression obligation at [${body},${body + "value".length}): evidence search failed: no derivation of its return-contract claim`);
  const escaped = structuredClone(returnedClaims);
  const outside = must(must(escaped.functions[0], "the containing function").expressions.find(
    (e) => e.pos[0] > outer.pos[1] && Array.isArray(e.type)), "an expression after the closure");
  outside.type = nested.type;
  assert.match(invoke(writeClaims(returned, "forged-escape", escaped), join(returned, "evidence.json"), returned),
    /is not in scope/);
}
{
  for (const [file, witness] of [
    ["invalid-nullish-field-write", "(() => { const x = { child: { b: 1 } }; return invalid(x, x); })()"],
    ["invalid-nullish-field-call", "(() => { const x = { child: { b: 1 } }; return invalid(x, () => { x.child = null; }); })()"],
    ["invalid-nullish-field-pattern", "invalid({ child: { b: 1 } })"],
    ["invalid-nullish-field-undefined", "invalid({})"],
  ]) {
    assert.ok(file && witness);
    assert.throws(() => runExample(file, witness), /Cannot read properties/);
  }
  const artifacts = run("nullish-field-observations");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  // The null branch cannot establish the opposite field observation.
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find((f) => f.name === "direct"), "direct function");
  const start = source.indexOf("return 0;", source.indexOf("function direct("));
  const guarded = must(fn.entries.find((e) => source.startsWith("return x.child.b;", e.start)), "guarded read entry");
  const known = must(guarded.bindings.find((b) => b.name === "x"), "guarded object");
  const unguarded = must(fn.entries.find((e) => e.start === start), "null branch entry");
  must(unguarded.bindings.find((b) => b.name === "x"), "null branch object").current = structuredClone(known.current);
  const forged = writeClaims(artifacts, "forged-non-null-field", claims);
  refusedAt(artifacts, forged, "forged-non-null-field",
    `source incoming edge obligation at [${start},${start + "return 0;".length})`);
  invoke(forged, join(artifacts, "evidence.json"), artifacts);

  // A pattern read's proposed result is independently checked at that read.
  const patternClaims = readClaims(artifacts);
  const nested = must(patternClaims.functions.find((f) => f.name === "nested"), "nested function");
  const read = must(nested.expressions.find((e) => source.slice(e.pos[0], e.pos[1]) === "b" &&
    source.slice(0, e.pos[0]).lastIndexOf("const {") > source.slice(0, e.pos[0]).lastIndexOf("return")), "pattern b read");
  read.type = [rowOf(patternClaims, "nul")];
  const badRead = writeClaims(artifacts, "forged-pattern-field-read", patternClaims);
  refusedAt(artifacts, badRead, "forged-pattern-field-read",
    `source expression obligation at [${read.pos[0]},${read.pos[1]})`);
  invoke(badRead, join(artifacts, "evidence.json"), artifacts);
}
{
  const artifacts = run("optional-read-observations");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find((f) => f.name === "observeOnly"), "optional observation function");
  const undef = rowOf(claims, "undef");
  const entry = must(fn.entries.find((e) => e.bindings.some((b) =>
    b.name === "obj" && b.current?.some(([key, type]) => key === "val" &&
      type.length === 1 && type[0] === undef))), "undefined branch entry");
  const object = must(entry.bindings.find((b) => b.name === "obj"), "observed object");
  // The undefined branch cannot establish a number-valued read observation.
  object.current = [["val", [rowOf(claims, "num")]]];
  const forged = writeClaims(artifacts, "forged-optional-read-result", claims);
  refusedAt(artifacts, forged, "forged-optional-read-result", "source incoming edge obligation");
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
  assert.equal(runExample("invalid-optional-read-alias", "stale({ val: undefined })"), 1);
  assert.equal(runExample("invalid-optional-read-call",
    "(() => { const obj = { val: undefined }; return stale(obj, () => { obj.val = 1; }); })()"), 1);
}
{
  // A void parameter admits numbers and objects as well as undefined.
  // A forged singleton claim must fail at the parameter read.
  const artifacts = run("void-source-values");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "compareArguments"), "compareArguments's claims");
  const at = source.indexOf("left !== right");
  must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + 4),
    "the void argument read").type = [rowOf(claims, "undef")];
  const forged = writeClaims(artifacts, "forged-void-undefined", claims);
  refusedAt(artifacts, forged, "forged-void-undefined",
    `source expression obligation at [${at},${at + 4})`);
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
}
{
  // An unconstrained source generic admits unknown, but its independently
  // extracted bound excludes calculus top and its internal stores.
  const artifacts = run("generic-unknown-arguments");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "forward"), "forward's claims");
  const at = source.indexOf("identity(value)", source.indexOf("function forward"));
  const call = must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + "identity(value)".length),
    "the generic identity call");
  const argument = must(call.instantiate?.[0], "identity's type argument");
  argument.type = [claims.types.length];
  claims.types.push(["top"]);
  const forged = writeClaims(artifacts, "forged-source-generic-top", claims);
  refusedAt(artifacts, forged, "forged-source-generic-top",
    `source direct obligation at [${at},${at + "identity(value)".length})`);
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
}
checkGenericRest(verifier, run("generic-rest"));
checkRestPackInstance(verifier, run("rest-pack-declared"), "emptyInfer()");
checkRestPackInstance(verifier, run("class-rest-binder"), "new RestRunner(\n");
checkOverloads(verifier, run("overloads"));
checkDefaults(verifier, run("default-parameter-scope"));
checkPatternDefaults(verifier, run("destructuring-known-default"));
checkEarlyDefault(verifier, run("invalid-default-invocation"));
checkSchemeDefaults(verifier, run("generic-default"));
process.stdout.write("forged claims at each kind of point: read and checked there\n");

{
  // Own-key exclusion preserves the inherited constructor read. A forged
  // undefined claim must fail both search and evidence consumption.
  const artifacts = run("native-promise-constructor-read");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "constructorValue"), "constructorValue's claims");
  const at = source.indexOf("p.constructor");
  must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + "p.constructor".length),
    "the inherited constructor read").type = [rowOf(claims, "undef")];
  const forged = writeClaims(artifacts, "forged-native-constructor-undefined", claims);
  refusedAt(artifacts, forged, "forged-native-constructor-undefined",
    `source expression obligation at [${at},${at + "p.constructor".length})`);
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
  // A fresh source object has no native promise prototype or identity.
  // Forging a native claim at its allocation must fail both verifier entries.
  const allocatedClaims = readClaims(artifacts);
  const allocatedFn = must(allocatedClaims.functions.find(f => f.name === "freshRecord"), "freshRecord's claims");
  const allocatedAt = source.indexOf("{}", source.indexOf("function freshRecord"));
  must(allocatedFn.expressions.find(e => e.pos[0] === allocatedAt && e.pos[1] === allocatedAt + 2),
    "the fresh record allocation").type = must(allocatedFn.params.find(p => p.name === "p"), "the native parameter").type;
  const allocated = writeClaims(artifacts, "forged-native-introduction", allocatedClaims);
  refusedAt(artifacts, allocated, "forged-native-introduction",
    `source expression obligation at [${allocatedAt},${allocatedAt + 2})`);
  invoke(allocated, join(artifacts, "evidence.json"), artifacts);
  // A forged proposal for a direct write starts with a valid native input.
  // Borrow evidence from a weakened constructor contract, then require the
  // native contract to refuse it at its ordinary write obligation.
  const write = run("invalid-native-promise-constructor-write");
  const weakAst: Ast = JSON.parse(readFileSync(join(write, "fragment.json"), "utf8"));
  const promise = must(weakAst.declarations.definitions.find(d =>
    d.declaration.name === "Promise" && d.declaration.module.startsWith("typescript/lib/")),
    "the native Promise declaration");
  assert(promise.expression.k === "object" && promise.expression.prototype?.k === "object");
  promise.expression.prototype.fields = promise.expression.prototype.fields.filter(f => f.name !== "constructor");
  promise.expression.fields.push({ name: "constructor", optional: false, readonly: false,
    type: { k: "atom", name: "unknown", span: [0, 0] }, span: [0, 0] });
  const weak = join(write, "weakened-native-constructor.json");
  writeFileSync(weak, JSON.stringify(weakAst));
  const lowered = spawnSync(verifier, ["--lower-control-flow", weak], { encoding: "utf8", timeout: 30_000 });
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(write, "weakened-native-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposed = spawnSync(producerExecutable, [weak, flow], { encoding: "utf8", timeout: 30_000 });
  assert.equal(proposed.status, 0, proposed.stderr);
  const borrowedClaims = join(write, "weakened-native-claims.json");
  writeFileSync(borrowedClaims, proposed.stdout);
  const borrowed = produceWith(write, borrowedClaims, "weakened-native-constructor", weak);
  assert.equal(borrowed.status, 0, borrowed.stdout + borrowed.stderr);
  const refusedWrite = produceWith(write, borrowedClaims, "forged-native-constructor-write");
  assert.equal(refusedWrite.status, 1, refusedWrite.stdout + refusedWrite.stderr);
  const writeFailure = readDiagnostic(refusedWrite.stdout + refusedWrite.stderr);
  assert.equal(writeFailure?.kind, "node-typing");
  assert.ok(writeFailure?.source?.sourceMap?.pos, "the native write refusal is located");
  assert.ok(writeFailure?.sequent && typeof writeFailure.sequent.term === "object" && "writeAt" in writeFailure.sequent.term);
  assert.equal(writeFailure.sequent.term.writeAt.field, "constructor");
  invoke(borrowedClaims, join(write, "weakened-native-constructor-evidence.json"), write);
  // The verifier interprets these impossible native input annotations before
  // consuming any evidence. It refuses them independently of producer choices.
  for (const file of ["invalid-native-promise-constructor-intersection", "invalid-native-promise-array-then"]) {
    const invalid = run(file);
    const searched = produceWith(invalid, join(invalid, "claims.json"), "native-input-annotation");
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.match(searched.stdout + searched.stderr, /intersection is empty/);
    assert.match(invoke(join(invalid, "claims.json"), join(artifacts, "evidence.json"), invalid),
      /intersection is empty/);
  }
}

{
  // Widening a generic wrapper's result preserves its input qualification.
  // Forging an unbounded target must fail search and accepted-evidence replay.
  const artifacts = run("native-promise-qualified-return");
  const ast: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
  const target = must(ast.declarations.definitions.find(d => d.declaration.name === "NumericUnknownWrapper"),
    "the result-widened generic wrapper declaration").expression;
  assert.ok(target.k === "scheme" && target.binders.length === 1);
  must(target.binders[0], "the retained numeric input binder").bound = null;
  const forged = join(artifacts, "forged-generic-input-bound.json");
  writeFileSync(forged, JSON.stringify(ast));
  const claims = join(artifacts, "claims.json");
  const searched = produceWith(artifacts, claims, "forged-generic-input-bound", forged);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("wrapper;", source.indexOf("function widenResult"));
  assert.ok((searched.stdout + searched.stderr).includes(
    `source expression obligation at [${at},${at + "wrapper".length})`), searched.stdout + searched.stderr);
  invoke(claims, join(artifacts, "evidence.json"), artifacts, forged);
}

{
  // Scheme matching must keep both the native receiver bound and finally's
  // fixed cleanup result contract. These forged methods broaden one operand.
  const artifacts = run("native-promise-reactions");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("p.finally");
  for (const part of ["receiver", "cleanup"] as const) {
    const claims = readClaims(artifacts);
    const fn = must(claims.functions.find(f => f.name === "finalized"), "finalized's claims");
    const method = must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + "p.finally".length),
      "finally's read claim").type;
    assert.ok(Array.isArray(method) && method.length === 1 && typeof method[0] === "number");
    const row = must(claims.types[method[0]], "finally's callable row");
    const arrow = must(row.flatMap(c => typeof c === "object" && "arrs" in c ? c.arrs.arrows : [])
      .find(a => a.arguments.length === 1), "finally's method signature");
    const top = [rowOf(claims, "top")];
    if (part === "receiver") arrow.receiver = top;
    else {
      const callback = must(arrow.arguments[0].flatMap(label => typeof label === "number" ?
        must(claims.types[label], "the cleanup row").flatMap(c =>
          typeof c === "object" && "arrs" in c ? c.arrs.arrows : []) : [])
        .find(a => a.arguments.length === 0), "the cleanup signature");
      callback.result = top;
    }
    const forged = writeClaims(artifacts, `forged-finally-${part}`, claims);
    refusedAt(artifacts, forged, `forged-finally-${part}`,
      `source expression obligation at [${at},${at + "p.finally".length})`);
    invoke(forged, join(artifacts, "evidence.json"), artifacts);
  }
}

{
  // A qualified instance's input is classified by its certificate: forging
  // Promise.resolve's input to the promise's open payload, or an async
  // return's input to unknown, leaves the proposed certificate unestablished,
  // also where the source result is independently widened.
  for (const [file, functionName] of [
    ["native-promise-resolve-identity", "nativeIdentity"],
    ["native-promise-qualified-return", "stableUnknown"],
    ["native-promise-qualified-return", "adoptUnknown"],
  ] as const) {
    const artifacts = run(file);
    const claims = readClaims(artifacts);
    const fn = must(claims.functions.find(f => f.name === functionName), `${functionName}'s claims`);
    const site = must(fn.expressions.find(e => e.instantiate?.some(i => i.name === "X" && i.resolution)),
      "the consumed intrinsic instance");
    const image = must(site.instantiate?.find(i => i.name === "X"), "the payload instance");
    image.type = functionName === "nativeIdentity" ? { param: "A" } : [rowOf(claims, "top")];
    const name = `forged-native-payload-${functionName}`;
    const forged = writeClaims(artifacts, name, claims);
    const searched = produceWith(artifacts, forged, name);
    const detail = searched.stdout + searched.stderr;
    assert.equal(searched.status, 1, detail);
    assert.ok(detail.includes(`source refusal at [${site.pos[0]},${site.pos[1]})`), detail);
    assert.match(detail, /resolution certificate does not establish/);
    assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts),
      /resolution certificate does not establish/);
  }
}

for (const [file, arity, accepted] of [
  ["closure-result-contract", 2, true], ["closure-graph-captured-cell", 0, false],
] as const) {
  const artifacts = run(file);
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf(accepted ? "(p: number" : "(): void");
  const closure = must(claims.functions.flatMap(f => f.expressions).find(e => e.pos[0] === at),
    "the callback's source claim");
  assert.ok(Array.isArray(closure.type) && closure.type.length === 1);
  const label = closure.type[0];
  assert.ok(typeof label === "number");
  const row = must(claims.types[label], "the callback's type row");
  const arrow = must(row.flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])
    .find(s => s.arguments.length === arity), "the callback contract");
  arrow.effect = "preservesInputHeap";
  const input = writeClaims(artifacts, "qualified-callback", claims);
  const produce = produceWith(artifacts, input, "qualified-callback");
  assert.ifError(produce.error);
  assert.equal(produce.signal, null);
  assert.equal(produce.status, accepted ? 0 : 1, produce.stdout + produce.stderr);
  if (accepted) {
    const consume = spawnSync(verifier, ["--check-source-claims", join(artifacts, "fragment.json"),
      input, join(artifacts, "source.ts"), join(artifacts, "qualified-callback-evidence.json")], {encoding: "utf8", timeout: 30_000});
    assert.ifError(consume.error);
    assert.equal(consume.status, 0, consume.stdout + consume.stderr);
  } else {
    const failure = readDiagnostic(produce.stdout + produce.stderr);
    assert.ok(failure && failure.kind === "node-typing", "a failed effect must name the callable's typing obligation");
    assert.ok(failure.source?.sourceMap?.pos, "the failed callable must have a source location");
  }
  process.stdout.write(`callback heap-preservation claim: ${accepted ? "certified" : "captured write refused"}\n`);
}

{
  const settled = outcomes[cases.findIndex(c => c.file === "invalid-explicit-type-argument-bound")];
  assert(settled?.status === "fulfilled" && settled.value.status === "unverified");
  const direct = readDiagnostic(settled.value.detail ?? "");
  assert(direct?.kind === "direct-obligation", "a direct failure needs a structured judgment");
  assert(!("statement" in direct.judgment), "direct judgments cannot store prose");
  const {input: _input, ...wire} = direct;
  const line = (value: unknown) => `obligation-diagnostic: ${JSON.stringify(value)}`;
  assert(readDiagnostic(line(wire)), "the structured direct judgment decodes");
  const unknown = structuredClone(wire);
  // Deliberately outside the typed union: the decoder must refuse it at run time.
  // Reflect keeps this malformed-wire test from weakening the typed source.
  Reflect.set(unknown.judgment, "kind", "future-judgment");
  assert.equal(readDiagnostic(line(unknown)), undefined, "an unhandled judgment variant is refused");
  const unscoped = structuredClone(wire);
  unscoped.judgment.actual = [wire.types.length];
  assert.equal(readDiagnostic(line(unscoped)), undefined, "a label outside the table is refused");
  const misplaced = structuredClone(wire);
  misplaced.sourceMap.pos = [0, 0];
  assert.equal(readDiagnostic(line(misplaced)), undefined, "a judgment cannot borrow another source span");
  process.stdout.write("direct obligation records: decoded, and malformed ones refused\n");
}
