// The pipeline's suite: every case of the inventory, then the forged
// documents and claims no case can make. The controls needing no build are
// node-runs.mts and trusted-inputs.mts, among the fast checks.
import assert from "node:assert/strict";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { Ast } from "../tools/fragment.mts";
import type { TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { check, producerExecutable, verifier } from "./verify-source.mts";
import { cases } from "./cases.mts";
import { expectOutcome, pooled, runCase } from "./run-cases.mts";
import type { Row, SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { emptyEffect, emptyFootprint, footprintEffect, ordinaryEffect, type ClosedFootprint } from "../tools/type-graph.mts";
// Forged-claim controls on single cases, each in a file of its own:
// generic-rest.mts, a universal rest claim past collection, substitution and binding;
// rest-pack-instance.mts, a forged non-array instance of a type parameter typing a value and a rest, at a call and at a `new`;
// overload-claims.mts, per-signature claims across the same independent boundary;
// default-parameters.mts, forged claims about parameter defaults: their scope, a generic closure's default, a capture read before its initialization.
import { checkGenericRest } from "./generic-rest.mts";
import { checkRestPackInstance } from "./rest-pack-instance.mts";
import { checkOverloads } from "./overload-claims.mts";
import { checkDefaults, checkSchemeDefaults, checkEarlyDefault, checkPatternDefaults } from "./default-parameters.mts";
import { decodeFlowDocument, type ExecutionPlan, type ExecutionOperation } from "../tools/source-flow.mts";
import { runExample } from "./run-example.mts";
const here = import.meta.dirname;

function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
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
/** The closed footprints other than the one letting everything change. */
const narrowerFootprints: ClosedFootprint[] = (["keep", "any"] as const).flatMap((value) =>
  (["keep", "grow", "any"] as const).map((store) => ({ value, store })))
  .filter((f) => f.value !== "any" || f.store !== "any");
const readClaims = (artifacts: string): SourceClaims =>
  JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
/** Write forged claims beside a run's artifacts. */
const writeClaims = (artifacts: string, name: string, claims: SourceClaims): string => {
  const path = join(artifacts, `${name}.json`);
  writeFileSync(path, JSON.stringify(claims));
  return path;
};

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
  assert(declaration?.expression?.k === "object");
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
    ({ k: "function", effect: ordinaryEffect, receiver: { k: "self", span }, params, rest, result, span });
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
    assert(d.expression?.k === "object");
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
    assert(d.expression?.k === "object");
    const next = must(d.expression.fields.find((f) => f.name === "next"), "Box's next").type;
    assert(next.k === "union");
    d.expression = { k: "union", parts: [{ k: "parameter", index: 0, span }, must(next.parts[0], "Box<[T]>")], span };
  });
  assert.equal(unguarded.status, 1);
  assert.match(unguarded.detail, /unguarded alias cycle through Box: a recursive alias must reach itself through an object, array, tuple or function type/);
  // A written application's obligation is what the document states: the
  // verifier checks each supplied entry at its arguments, its target's
  // bounds and its scope's assumptions (the front end supplies every one).
  const forgeDocument = (artifacts: string, file: string, change: (fragment: Ast) => void) => {
    const fragment: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
    change(fragment);
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    const searched = produceWith(artifacts, join(artifacts, "claims.json"), file, path);
    return { status: searched.status, detail: searched.stdout + searched.stderr };
  };
  const scopes = run("written-scopes");
  const dependent = (fragment: Ast) => must(fragment.declarations.applications.find(a =>
    a.site.endsWith("#dependent")), "dependent's B<U>");
  const widened = forgeDocument(scopes, "forged-written-argument", fragment => {
    const entry = dependent(fragment);
    entry.args = [{ k: "atom", name: "number", span }];
  });
  assert.equal(widened.status, 1, widened.detail);
  assert.match(widened.detail, /a written application: the type argument for B's "T" .*does not establish its declared bound: number ≤ string/);
  const weakened = forgeDocument(scopes, "forged-written-scope", fragment => {
    const entry = dependent(fragment);
    for (const level of entry.scope) for (const binder of level) binder.bound = null;
  });
  assert.equal(weakened.status, 1, weakened.detail);
  assert.match(weakened.detail, /a written application: the type argument for B's "T" .*does not establish its declared bound/);
  const relaxed = forgeDocument(run("invalid-computed-bound-typeof"), "forged-written-bound", fragment => {
    const entry = must(fragment.declarations.applications.find(a => a.reference.name === "BoxOf"), "BoxOf<number>");
    entry.bounds = entry.bounds.map(() => null);
  });
  assert.equal(relaxed.status, 0, relaxed.detail);
  // A reference carries every argument, the omitted ones completed where it
  // is read: one left short, for the checker to complete with a default, is
  // refused.
  const short = forgeDocument(run("written-dependent-default"), "forged-short-reference", fragment => {
    const found: unknown[] = [];
    const walk = (value: unknown): void => {
      if (Array.isArray(value)) value.forEach(walk);
      else if (value && typeof value === "object") {
        if ("k" in value && value.k === "reference" && "args" in value && Array.isArray(value.args) &&
            "reference" in value && JSON.stringify(value.reference).includes('"name":"Keys"')) found.push(value.args);
        Object.values(value).forEach(walk);
      }
    };
    walk(fragment.functions);
    for (const args of found) if (Array.isArray(args)) args.pop();
    assert.ok(found.length, "a reference to Keys");
  });
  assert.equal(short.status, 1, short.detail);
  assert.match(short.detail, /Keys applied to 1 type arguments of 2/);
  // A written obligation whose comparison runs out of rounds is refused as
  // exhausted, at the application (`Node<Leaf>`), not verified.
  const exhausted = check(join(here, "examples", "written-recursive-bound.ts"), undefined, false, 0);
  assert.equal(exhausted.status, "exhausted", JSON.stringify(exhausted));
  assert("detail" in exhausted);
  assert.match(exhausted.detail, /source direct obligation at \[202,212\): subtype search exhausted/);
}
{
  // A parameter's entry claim in an `&&` operand is its first read before a
  // call, which the incoming edge checks: a read claimed narrower than any
  // test establishes is refused where evidence is produced and where it is
  // checked.
  const good = run("logical-narrowing-past-reads");
  const source = readFileSync(join(good, "source.ts"), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "untested"), "untested function");
  const start = source.indexOf("Number.isSafeInteger(v);\n}\n", source.indexOf("function untested")) + "Number.isSafeInteger(".length;
  const read = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 1), "the read of v");
  read.type = [rowOf(claims, "num")];
  const forged = writeClaims(good, "untested-number", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(verifier, [mode, join(good, "fragment.json"), forged,
      join(good, "source.ts"), join(good, mode === "--produce-source-claims"
        ? "untested-number-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
  }
  process.stdout.write("forged operand entry: a parameter read claimed narrower than its test refused\n");
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
    "ctors" in clause ? clause.ctors.signatures.map((s) => s.arguments) : []));
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
  // Each run reaches a field that is null or absent and throws there: where
  // the source verifies, the nested read's guard throws as JavaScript does.
  for (const [file, witness] of [
    ["nullish-field-write-throws", "(() => { const x = { child: { b: 1 } }; return invalid(x, x); })()"],
    ["nullish-field-call-throws", "(() => { const x = { child: { b: 1 } }; return invalid(x, () => { x.child = null; }); })()"],
    ["invalid-nullish-field-pattern", "invalid({ child: { b: 1 } })"],
    ["nullish-field-undefined-refused", "invalid({})"],
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
  assert(promise.expression?.k === "object" && promise.expression.prototype?.k === "object");
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
  const writeTerm = writeFailure?.sequent?.term;
  assert.ok(writeTerm?.kind === "writeAt");
  assert.equal(writeTerm.field, "constructor");
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
  assert.ok(target?.k === "scheme" && target.binders.length === 1);
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

// A footprint claim forged onto a callback is certified only where its body
// is within it: one reading its arguments is within the empty footprint; one
// writing a cell it captures, a `Map`'s internal slots through `set`, or a
// fresh `Set`'s through `add` is within `{value: any, store: keep}` and not
// the empty one; one calling a member stated unrestricted (`pop` on the source
// beside a string's `trim` or alone) or beyond the footprint (a global regex's
// `test`) is refused at its own typing, even at the footprint `map`'s dense
// signature accepts. A refused control marked `consumed` also checks the
// fixture's honest evidence against the forged claim, which must refuse; its
// fixture verifies, so that evidence exists: program 7 at a result type
// admitting holes (`map-unstable-pop-sparse`) is consumed so. A negative
// fixture has no evidence, and its control is production only.
const keepAll: ClosedFootprint = { value: "keep", store: "keep" };
const writeValues: ClosedFootprint = { value: "any", store: "keep" };
const growStores: ClosedFootprint = { value: "any", store: "grow" };
for (const [file, marker, arity, accepted, footprint, consumed] of [
  ["closure-result-contract", "(p: number", 2, true, keepAll, true],
  ["closure-graph-captured-cell", "(): void", 0, false, keepAll, true],
  ["invalid-map-primitive-method-mutation", "(x: string)", 3, false, keepAll, false],
  ["map-stable-regexp-test", "(l) => word", 3, false, keepAll, true],
  ["map-stable-collection-write", "(name) =>", 3, false, keepAll, true],
  ["map-stable-collection-write", "(name) =>", 3, true, writeValues, true],
  ["map-stable-set", "(ys: readonly", 3, false, keepAll, true],
  ["map-stable-set", "(ys: readonly", 3, true, writeValues, true],
  ["map-stable-outer-cell", "(x: number)", 3, false, keepAll, true],
  ["map-stable-outer-cell", "(x: number)", 3, true, writeValues, true],
  ["invalid-map-unstable-pop", "(x: number)", 3, false, growStores, false],
  ["map-unstable-pop-sparse", "(x: number)", 3, false, growStores, true],
  ["map-stable-fresh-store", "(l) =>", 3, false, keepAll, true],
  ["map-stable-fresh-store", "(l) =>", 3, true, writeValues, true],
  ["invalid-map-fresh-alias", "(x) =>", 3, false, writeValues, false],
  ["invalid-map-fresh-join", "(x) =>", 3, false, writeValues, false],
  ["invalid-map-fresh-reassigned", "(x) =>", 3, false, writeValues, false],
  ["invalid-map-fresh-parameter", "(x) =>", 3, false, writeValues, false],
  ["map-fresh-handler-refused", "(x) =>", 3, false, writeValues, false],
  ["invalid-map-handler-after-pop", "(x) =>", 3, false, writeValues, false],
  ["map-fresh-controls-sparse", "(x) =>", 3, false, writeValues, true],
  ["map-fresh-controls-sparse", "(y) =>", 3, false, writeValues, true],
  ["map-fresh-controls-sparse", "(z) =>", 3, false, writeValues, true],
  ["map-fresh-controls-sparse", "(w) =>", 3, false, writeValues, true],
] as const) {
  const artifacts = run(file);
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf(marker);
  const closure = must(claims.functions.flatMap(f => f.expressions).find(e => e.pos[0] === at),
    "the callback's source claim");
  assert.ok(Array.isArray(closure.type) && closure.type.length === 1);
  const label = closure.type[0];
  assert.ok(typeof label === "number");
  const row = must(claims.types[label], "the callback's type row");
  const arrow = must(row.flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])
    .find(s => s.arguments.length === arity), "the callback contract");
  arrow.effect = footprintEffect(footprint);
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
    // Checking the honest evidence, where the case has any, against the
    // forged claim is a located footprint refusal: at a node of the closure
    // search named, or of a unit whose call of it the forged type no longer
    // admits at the signature the evidence selected.
    const callable = must(failure.source?.sourceMap?.pos, "the failed callable's source location");
    assert.equal(existsSync(join(artifacts, "evidence.json")), consumed,
      `${file}: a consumed control needs the fixture's honest evidence, a production-only one has none`);
    if (consumed) {
      const checked = invoke(input, join(artifacts, "evidence.json"), artifacts);
      const refused = /source effect refusal at \[(\d+),(\d+)\): the footprint claimed for (a closure|')/.exec(checked);
      assert.ok(refused, checked);
      if (refused[3] === "a closure")
        assert.ok(callable[0] <= Number(refused[1]) && Number(refused[2]) <= callable[1],
          `checking refused at [${refused[1]},${refused[2]}), outside the closure [${callable[0]},${callable[1]})`);
    }
  }
  process.stdout.write(`callback footprint claim {${footprint.value}, ${footprint.store}}, ${file}: ${accepted ? "certified" : consumed ? "refused in search and in checking" : "refused in search"}\n`);
}

{
  // `split`'s non-empty form is selected by its separator's type: the
  // separator `"\n"` forged at `string` takes the general form, whose first
  // element may be undefined, so search refuses it, and checking the honest
  // evidence, which selected the non-empty form, refuses it there.
  const artifacts = run("split-non-empty");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf('"\\n"');
  const separator = must(claims.functions.flatMap(f => f.expressions).find(e => e.pos[0] === at),
    "the separator's claim");
  const str = claims.types.findIndex(row => JSON.stringify(row) === JSON.stringify(["str"]));
  assert.ok(str >= 0 && Array.isArray(separator.type) && !separator.type.includes(str));
  separator.type = [str];
  const input = writeClaims(artifacts, "forged-split-separator", claims);
  const produce = produceWith(artifacts, input, "forged-split-separator");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts), /reject|source expression obligation/);
  process.stdout.write("forged split separator: a separator claimed at string refused in search and in checking\n");
}

{
  // The non-empty form's store contract forbids a removal: a call whose
  // result is shrunk (popped, through an alias) or held at `string[]`, its
  // honest evidence at the general form, forged at `[string, ...string[]]`,
  // is refused in search and in checking, whatever the producer proposes.
  const artifacts = run("split-non-empty");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  for (const name of ["popped", "aliasShrunk", "annotated"]) {
    const claims = readClaims(artifacts);
    const call = 'text.split(",")';
    const at = source.indexOf(call, source.indexOf(`function ${name}(`));
    const claim = must(claims.functions.flatMap(f => f.expressions).find(e => e.pos[0] === at && e.pos[1] === at + call.length),
      `${name}'s split claim`);
    const str = claims.types.findIndex(row => JSON.stringify(row) === JSON.stringify(["str"]));
    assert.ok(str >= 0);
    claims.types.push([{ list: { first: { required: [[str]], optional: [], rest: [str], readonly: false, presence: "dense" }, rest: [] } }]);
    claim.type = [{ array: [claims.types.length - 1], readonly: false }];
    const input = writeClaims(artifacts, `forged-split-tuple-${name}`, claims);
    const produce = produceWith(artifacts, input, `forged-split-tuple-${name}`);
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, `${name}: ${produce.stdout}${produce.stderr}`);
    assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts), /reject|source expression obligation/, name);
  }
  process.stdout.write("forged split tuple: shrunk, aliased and annotated results claimed non-empty refused in search and in checking\n");
}

{
  // A receiver claimed without its `undefined` takes no nullish guard: the
  // read of `b` in `b.n`, a parameter that may be absent, forged at the box
  // alone, is refused in search, and checking the honest evidence, whose
  // guard the forged claim no longer lowers, refuses it there.
  const artifacts = run("nullish-member-reads");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("b.n;", source.indexOf("function size("));
  const receiver = must(claims.functions.flatMap(f => f.expressions).find(e => e.pos[0] === at && e.pos[1] === at + 1),
    "the receiver's claim");
  const undef = claims.types.findIndex(row => JSON.stringify(row) === JSON.stringify(["undef"]));
  assert.ok(Array.isArray(receiver.type) && receiver.type.includes(undef), "the honest receiver admits undefined");
  receiver.type = receiver.type.filter(label => label !== undef);
  const input = writeClaims(artifacts, "forged-nullish-receiver", claims);
  const produce = produceWith(artifacts, input, "forged-nullish-receiver");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts), /source expression obligation|reject/);
  process.stdout.write("forged nullish receiver: a receiver claimed without undefined refused in search and in checking\n");
}

{
  // A fresh result forged onto code returning its parameter, a constant whose
  // value a callback pops: the code's returns are checked to return a store
  // allocated by its run, and the parameter's is not, so search refuses the
  // claim and checking the honest evidence against it refuses it there.
  const artifacts = run("map-stable-fresh-store");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("(a: string[])");
  const closure = must([...claims.functions.flatMap(f => f.expressions), ...(claims.init?.expressions ?? [])]
    .find(e => e.pos[0] === at), "the constant's closure claim");
  assert.ok(Array.isArray(closure.type) && closure.type.length === 1);
  const label = closure.type[0];
  assert.ok(typeof label === "number");
  const arrows = must(claims.types[label], "the closure's type row").flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []);
  assert.ok(arrows.length > 0 && arrows.every(a => !a.effect.fresh), "the honest claim states no fresh result");
  for (const arrow of arrows) arrow.effect = { ...arrow.effect, fresh: true };
  const input = writeClaims(artifacts, "forged-fresh-result", claims);
  const produce = produceWith(artifacts, input, "forged-fresh-result");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts),
    /source effect refusal at \[\d+,\d+\): the footprint claimed for a closure/);
  process.stdout.write("forged fresh result: code returning its parameter refused in search and in checking\n");
}

{
  // A footprint claim forged onto classes' construct signatures is checked
  // against their constructors' code: constructors writing their instances'
  // fields are refused within the empty footprint, at their own typing,
  // located in a class; the honest evidence checked against the forged claim
  // is a footprint refusal located there too.
  const artifacts = run("class-constructor-default");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const classes: [number, number] = [source.indexOf("class Counter"), source.indexOf("export function")];
  const within = (at: [number, number]) => classes[0] <= at[0] && at[1] <= classes[1];
  const signatures = claims.types.flatMap(row => row.flatMap(clause =>
    typeof clause === "object" && "ctors" in clause ? clause.ctors.signatures : []));
  assert.ok(signatures.length > 0, "the classes' construct signatures");
  for (const signature of signatures) signature.effect = footprintEffect(keepAll);
  const input = writeClaims(artifacts, "qualified-constructor", claims);
  const produce = produceWith(artifacts, input, "qualified-constructor");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const failure = readDiagnostic(produce.stdout + produce.stderr);
  assert.ok(failure && failure.kind === "node-typing", produce.stdout + produce.stderr);
  const pos = must(failure.source?.sourceMap?.pos, "the failed class's source location");
  assert.ok(within(pos), `refused at [${pos[0]},${pos[1]}), outside the classes`);
  const checked = invoke(input, join(artifacts, "evidence.json"), artifacts);
  const refused = must(/source effect refusal at \[(\d+),(\d+)\)/.exec(checked), checked);
  assert.ok(within([Number(refused[1]), Number(refused[2])]), checked);
  process.stdout.write("construct footprint claim {keep, keep}, class-constructor-default: refused\n");
}

{
  // A construction forged to the other stated form's result: `new Set` of a
  // string claimed at the `Set<number>` the array construction has. The
  // construction rule requires the selected signature with every argument's
  // premise, so search refuses it, and so does checking the honest evidence
  // against the forged claim.
  const artifacts = run("set-string-construction");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const expressions = claims.functions.flatMap(f => f.expressions);
  const at = (text: string) => must(expressions.find(e => e.pos[0] === source.indexOf(text) &&
    e.pos[1] === source.indexOf(text) + text.length), `the claim of ${text}`);
  at("new Set(word)").type = at("new Set<number>(codes)").type;
  const input = writeClaims(artifacts, "forged-set-form", claims);
  const produce = produceWith(artifacts, input, "forged-set-form");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts), /reject/);
  process.stdout.write("forged construct form: a string's set claimed at Set<number> refused in search and in checking\n");
}

{
  // An optional call's body is claimed at no value only where its receiver
  // is only nullish. The loop's receiver holds the array from the second
  // iteration on: the body's member read and call forged to no value are
  // refused, whatever the producer proposes.
  const artifacts = run("optional-call-loop-cell");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const start = source.indexOf("?.push");
  const forged = claims.functions.flatMap(f => f.expressions).filter(e => e.pos[0] === start);
  assert.ok(forged.length > 0, "the optional body's claims");
  // The empty union: no value.
  for (const e of forged) e.type = [];
  const input = writeClaims(artifacts, "forged-dead-optional-body", claims);
  const produce = produceWith(artifacts, input, "forged-dead-optional-body");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  process.stdout.write("forged dead optional body: refused where the receiver may be present\n");
}

{
  // A module constant's arrow is claimed at its signature extended by a rest
  // of `unknown`, which Lean checks against the arrow itself: the extension
  // forged to take `unknown` at the arrow's `string` parameter is refused
  // where the arrow is created.
  const artifacts = run("arrow-constant-callback");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const init = must(claims.init, "the initialization unit's claims");
  const closure = must(init.expressions.find(e => e.pos[0] === source.indexOf("(s: string): string => s.toUpperCase")),
    "the constant's arrow claim");
  const label = Array.isArray(closure.type) ? closure.type[0] : undefined;
  assert.ok(typeof label === "number");
  const row = must(claims.types[label], "the arrow's type row");
  const extended = must(row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.variadic ?? [] : [])[0],
    "the extended signature");
  const unknown = claims.types.findIndex(r => JSON.stringify(r) === JSON.stringify(["source"]));
  assert.ok(unknown >= 0, "a row of unknown");
  extended.arguments = [[[unknown]], must(extended.arguments[1], "the extended signature's rest")];
  const input = writeClaims(artifacts, "forged-constant-extension", claims);
  const produce = produceWith(artifacts, input, "forged-constant-extension");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  // The row is shared by both constants of that signature, `shout` and
  // `quoted`: the first checked is refused.
  const refused = /direct obligation at \[(\d+),\d+\): closure signature claim is outside the source annotation/
    .exec(produce.stdout + produce.stderr);
  assert.ok(refused, produce.stdout + produce.stderr);
  assert.ok([source.indexOf("(s: string): string => s.toUpperCase"), source.indexOf("function (s: string)")]
    .includes(Number(refused[1])), "refused at a constant's closure");
  process.stdout.write("forged constant extension: refused where the arrow is created\n");
}

{
  // `%Dispatch:replace%` states heap preservation only at a target whose
  // `[Symbol.replace]` states it. A global regex's does not: an instance of
  // the dispatch claimed preserving at that target, with the callback
  // claimed preserving through it, is refused at the callback's typing,
  // whatever the producer proposes, and checking the honest evidence against
  // the forged claims is a footprint refusal.
  const artifacts = run("map-stable-regexp-replace");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const expressions = claims.functions.flatMap(f => f.expressions);
  const arrowAt = (start: number, arity: number) => {
    const claim = must(expressions.find(e => e.pos[0] === start && Array.isArray(e.type) && e.type.length === 1),
      `the claim at ${start}`);
    const label = Array.isArray(claim.type) ? claim.type[0] : undefined;
    assert.ok(typeof label === "number");
    const row = must(claims.types[label], `the type row at ${start}`);
    return must(row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])
      .find(s => s.arguments.length === arity), `the contract at ${start}`);
  };
  arrowAt(source.indexOf("replace("), 3).effect = emptyEffect;
  arrowAt(source.indexOf("(l) =>"), 3).effect = emptyEffect;
  const input = writeClaims(artifacts, "forged-dispatch-effect", claims);
  const produce = produceWith(artifacts, input, "forged-dispatch-effect");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const failure = readDiagnostic(produce.stdout + produce.stderr);
  assert.ok(failure && failure.kind === "node-typing", "a forged dispatch effect must fail at a node's typing");
  assert.ok(existsSync(join(artifacts, "evidence.json")), "the fixture's honest evidence");
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts),
    /source effect refusal at \[\d+,\d+\): the footprint claimed for/);
  process.stdout.write("forged dispatch effect: a global regex's replacement refused in search and in checking\n");
}

{
  // A declaration's claimed footprint is established by its own unit's
  // graph. `collect` steps an array iterator, which writes its position,
  // and pushes onto its parameter: it is within `{value: any, store: grow}`
  // and verifies there. Claimed at a footprint not covering that one,
  // evidence production refuses at a node of its body, and the evidence for
  // the honest claims does not justify the forged ones.
  const artifacts = run("optional-call-loop-cell");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  for (const footprint of narrowerFootprints.filter((f) => f.value !== "any" || f.store === "keep")) {
    const claims = readClaims(artifacts);
    must(claims.functions.find(f => f.name === "collect"), "collect's claims").footprint = footprint;
    const name = `forged-declaration-footprint-${footprint.value}-${footprint.store}`;
    const input = writeClaims(artifacts, name, claims);
    const produce = produceWith(artifacts, input, name);
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, produce.stdout + produce.stderr);
    // Search and checking both name a node of `collect`'s loop.
    for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)]) {
      const refused = /source effect refusal at \[(\d+),\d+\): the footprint claimed for 'collect'/.exec(detail);
      assert.ok(refused, detail);
      const at = Number(refused[1]);
      assert.ok(source.indexOf("for (const line") <= at && at < source.indexOf("target = into") + "target = into".length,
        `refused in the loop, not at ${at}`);
    }
  }
  process.stdout.write("forged declaration footprints: each not covering the body's refused in its loop, in search and in checking\n");
}

{
  // A guard's promise is its annotation's: a guard declaration claimed
  // heap-preserving is refused at the declaration.
  const artifacts = run("type-guards");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const guard = must(claims.functions.find(f => f.name === "isPresence"), "isPresence's claims");
  assert.ok(source.slice(guard.namePos[1]).startsWith("(value: unknown): value is Presence"));
  guard.footprint = emptyFootprint;
  const input = writeClaims(artifacts, "forged-guard-effect", claims);
  refusedAt(artifacts, input, "forged-guard-effect",
    `source effect refusal at [${guard.namePos[0]},${guard.namePos[1]}): the footprint claimed for '${guard.name}'`);
  process.stdout.write("forged guard effect: refused at the guard declaration\n");
}

{
  // A footprint check that runs out of subtype rounds is inconclusive, not a
  // refusal: `marks` claims the empty footprint, and with one round the
  // checks of its graph exhaust. Search and checking report exhaustion, never
  // a footprint refusal.
  const file = join(here, "examples", "declaration-preserving-callback.ts");
  const searched = check(file, undefined, false, 1);
  assert.equal(searched.status, "exhausted", JSON.stringify(searched));
  const artifacts = run("declaration-preserving-callback");
  const checking = spawnSync(verifier, ["--subtype-rounds", "1", "--check-source-claims",
    join(artifacts, "fragment.json"), join(artifacts, "claims.json"), join(artifacts, "source.ts"),
    join(artifacts, "evidence.json")], { encoding: "utf8", timeout: 30_000 });
  assert.equal(checking.status, 1, checking.stdout + checking.stderr);
  const failure = readDiagnostic(checking.stdout + checking.stderr);
  assert.ok(failure && failure.outcome.kind === "exhausted", checking.stdout + checking.stderr);
  assert.doesNotMatch(checking.stdout + checking.stderr, /source effect refusal/);
  process.stdout.write("exhausted footprint check: reported as exhausted in search and in checking\n");
}

{
  // A footprint and an effect have one spelling: `grow` on a value, which
  // is `keep` there, and an effect without its promise field are refused
  // where the claims are read.
  const artifacts = run("optional-call-loop-cell");
  const evidence = join(artifacts, "evidence.json");
  const claims = readClaims(artifacts);
  const collect = must(claims.functions.find(f => f.name === "collect"), "collect's claims");
  const grown = join(artifacts, "forged-footprint-value-grow.json");
  writeFileSync(grown, JSON.stringify(claims, (key, value: unknown) =>
    key === "footprint" && value === collect.footprint ? { value: "grow", store: "keep" } : value));
  assert.match(invoke(grown, evidence, artifacts), /invalid footprint change 'grow'/);
  const arrow = must(claims.types.flatMap(row => row.flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []))[0], "a claimed arrow");
  const unpromised = join(artifacts, "forged-effect-without-promise.json");
  writeFileSync(unpromised, JSON.stringify(claims, (key, value: unknown) =>
    key === "effect" && value === arrow.effect ? { footprint: arrow.effect.footprint } : value));
  assert.match(invoke(unpromised, evidence, artifacts), /promise/);
  process.stdout.write("footprints and effects other than the one spelling: refused\n");
}

{
  // An imported function is read at its declaration's type, which states no
  // effect: its call claimed at any narrower footprint, with the callback
  // through it, is refused.
  const artifacts = run("invalid-preserving-callback-value-import");
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  for (const footprint of narrowerFootprints) {
    const claims = readClaims(artifacts);
    const expressions = claims.functions.flatMap(f => f.expressions);
    const arrowsAt = (start: number) => {
      const claim = must(expressions.find(e => e.pos[0] === start && Array.isArray(e.type) && e.type.length === 1),
        `the claim at ${start}`);
      const label = Array.isArray(claim.type) ? claim.type[0] : undefined;
      assert.ok(typeof label === "number");
      const row = must(claims.types[label], `the type row at ${start}`);
      return row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []);
    };
    const forged = [...arrowsAt(source.indexOf("double(x)")), ...arrowsAt(source.indexOf("(x) =>"))];
    assert.ok(forged.length > 0, "the callee's and the callback's contracts");
    for (const s of forged) s.effect = footprintEffect(footprint);
    const name = `forged-import-footprint-${footprint.value}-${footprint.store}`;
    const input = writeClaims(artifacts, name, claims);
    const produce = produceWith(artifacts, input, name);
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  }
  process.stdout.write("forged import footprints: an imported function's call refused each footprint narrower than everything\n");
}

{
  // A guard's promise is its function type's, checked at its body: the lying
  // guard's claims forged to hold its argument at `string` throughout the
  // body, and its answer at `true`, are refused at the edge into its
  // return, which holds the argument at the parameter's `unknown`.
  const artifacts = run("invalid-type-guard-promise");
  const claims = readClaims(artifacts);
  const guard = must(claims.functions.find((f) => f.name === "isString"), "the guard's claims");
  const x = must(guard.params[0], "the guard's parameter");
  const str = rowOf(claims, "str");
  const tru = rowOf(claims, { boolLit: { value: true } });
  for (const entry of guard.entries) for (const b of entry.bindings) if (b.name === x.name) b.type = [str];
  const read = must(guard.expressions.find((e) => e.pos[1] - e.pos[0] === x.name.length), "the read of the argument");
  for (const e of guard.expressions) e.type = e === read ? [str] : [tru];
  const forged = writeClaims(artifacts, "forged-guard-promise", claims);
  const searched = produceWith(artifacts, forged, "forged-guard-promise");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /source incoming edge obligation at \[271,300\): evidence search failed/);
  process.stdout.write("forged guard promise: refused at the guard's body\n");
}

{
  // A call narrows its argument by the promise the parser's document states
  // of its callee, never by the producer's claims: with the promise removed
  // from `isPresence`'s document, the producer's claims, which read
  // `isPresence` at its qualified signature, are refused at that read.
  const artifacts = run("type-guards");
  const fragment: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
  const isPresence = must(fragment.functions.find((f) => f.name === "isPresence"), "isPresence");
  assert.ok(isPresence.guard, "isPresence states a promise");
  isPresence.guard = null;
  const ast = join(artifacts, "forged-unpromised-guard.json");
  writeFileSync(ast, JSON.stringify(fragment));
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-unpromised-guard", ast);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const call = source.indexOf("isPresence(v)");
  assert.match(searched.stdout + searched.stderr,
    new RegExp(`source expression obligation at \\[${call},${call + "isPresence".length}\\): evidence search failed`));
  assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, ast), /obligation|evidence|claim/);
  process.stdout.write("unpromised guard call: its qualified read refused\n");
}

{
  // A closure's written promise is proved whatever the claims offer: with
  // the promise signature removed from the arrow constant `isNumber`'s claim,
  // and its body's claims for that signature, the closure is refused.
  const artifacts = run("type-guards");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("(v: unknown): v is number =>");
  const init = must(claims.init, "the module's claims");
  const arrow = must(init.arrows?.find((a) => a.pos[0] === at), "isNumber's arrow claims");
  const claim = must(init.expressions.find((e) => e.pos[0] === at && e.pos[1] === arrow.pos[1]), "isNumber's claim");
  const label = Array.isArray(claim.type) && claim.type.length === 1 ? claim.type[0] : undefined;
  assert.ok(typeof label === "number", "isNumber is claimed at one row");
  const clause = must(claims.types[label]?.[0], "isNumber's row");
  assert.ok(typeof clause === "object" && "arrs" in clause, "isNumber is claimed at arrows");
  const kept = clause.arrs.arrows.map((a) => a.effect.promise === null);
  assert.ok(kept.includes(false), "isNumber's claim offers its promise");
  clause.arrs.arrows = clause.arrs.arrows.filter((_, i) => kept[i]);
  arrow.rows = arrow.rows.filter((_, i) => kept[i]);
  const forged = writeClaims(artifacts, "forged-unoffered-promise", claims);
  refusedAt(artifacts, forged, "forged-unoffered-promise", "a guard closure's claim must offer its written promise over its annotated parameters");
  process.stdout.write("guard closure claimed without its promise: refused\n");
}

{
  // A closure's written promise is about every input its annotation admits:
  // with `isNumber`'s promise signature claimed at the parameter `number`,
  // where it holds of every argument, the closure is refused.
  const artifacts = run("type-guards");
  const claims = readClaims(artifacts);
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const at = source.indexOf("(v: unknown): v is number =>");
  const init = must(claims.init, "the module's claims");
  const arrow = must(init.arrows?.find((a) => a.pos[0] === at), "isNumber's arrow claims");
  const claim = must(init.expressions.find((e) => e.pos[0] === at && e.pos[1] === arrow.pos[1]), "isNumber's claim");
  const label = Array.isArray(claim.type) && claim.type.length === 1 ? claim.type[0] : undefined;
  assert.ok(typeof label === "number", "isNumber is claimed at one row");
  const clause = must(claims.types[label]?.[0], "isNumber's row");
  assert.ok(typeof clause === "object" && "arrs" in clause, "isNumber is claimed at arrows");
  const promise = must(clause.arrs.arrows.find((a) => a.effect.promise !== null), "isNumber's promise signature");
  promise.arguments = [promise.result];
  const forged = writeClaims(artifacts, "forged-narrowed-promise", claims);
  refusedAt(artifacts, forged, "forged-narrowed-promise", "a guard closure's claim must offer its written promise over its annotated parameters");
  process.stdout.write("guard closure's promise claimed over a narrower parameter: refused\n");
}
{
  // A regex literal's shape is the declared type of the intrinsic its call
  // names (`%RegExp:Σ%`, `regexp.mts`), which the front end lists from the
  // literal's pattern. A parser document naming at a literal a shape no
  // declaration lists (three groups always matched, where `/(\w+):/` has one)
  // is refused at both verifier entry points.
  const artifacts = run("regexp-structural");
  const text = readFileSync(join(artifacts, "fragment.json"), "utf8");
  const call = /"callee":\{"k":"id","pos":\[\d+,\d+\],"name":"%RegExp:1%"\}/.exec(text)?.[0];
  assert.ok(call, "a literal's call names its shape");
  const ast = join(artifacts, "forged-regexp-shape.json");
  writeFileSync(ast, text.replace(call, call.replace("%RegExp:1%", "%RegExp:111%")));
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-regexp-shape", ast);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /%RegExp:111%/);
  assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, ast),
    /%RegExp:111%/);
  process.stdout.write("forged regex shape: a literal naming a shape no declaration lists refused\n");
}
