// The pipeline's controls: the forged documents and claims no case can make,
// mutations of the verifier, injected tool failures and host-family
// overrides, each control run by a pool of control processes (`make test`).
// Every operation a control runs replays from the stage store like any stage
// (DESIGN.md, "The stage store"). The pipeline cases are run-cases.mts's.
import assert from "node:assert/strict";
import { chmodSync, cpSync, mkdirSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { present } from "../tools/files.mts";
import { join, resolve } from "node:path";
import type { Ast, Expr } from "../tools/fragment.mts";
import type { TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import { createHash } from "node:crypto";
import { availableParallelism } from "node:os";
import { pathToFileURL } from "node:url";
import { fork, spawn, spawnSync } from "node:child_process";
import { controlOperations, tested, ran as ranStage, readInvocationLog, type AttemptRecord, type Invoked }
  from "./stages.mts";
import { producerCall, verifierCall } from "./stage-execution.mts";
import { check, invocationLog, producerExecutable, readClaimsFile, readFragmentFile, readOutcome, sourceKey, verifier,
  type Outcome } from "./verify-source.mts";
import { runDirectory, runRoot } from "./run-directory.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { compilerApiFamily, hostEnums } from "../tools/compiler-api.mts";
import { useFamiliesForTests } from "../tools/family-activation.mts";
import type { FamilyDescription } from "../tools/host-families.mts";
import { stringFamily } from "./string-family.mts";
import { cases } from "./cases.mts";
import { expectOutcome } from "./run-cases.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { linkFixtures } from "./fixture-links.mts";
import type { Row, SourceClaims } from "../tools/source-claims.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { decodeGraph, emptyEffect, emptyFootprint, footprintEffect, ordinaryEffect, type ClosedFootprint } from "../tools/type-graph.mts";
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
import { checkMutation, forgedEvidence, mutationVerifier, useMutationVerifier } from "./evidence-mutations.mts";
const here = import.meta.dirname;

/** The controls, each a block of this file, registered in order. The
 * suite's process gives them to a pool of control processes, one per core
 * (`--controls`), each running one control at a time; a control running the
 * mutation verifier registers with `mutationControl` and is given once its
 * build, beside the others, is done. */
const controls: (() => Promise<void>)[] = [];
const mutationControls = new Set<number>();
const control = (body: () => Promise<void>): void => {
  controls.push(body);
};
const mutationControl = (body: () => Promise<void>): void => {
  mutationControls.add(controls.push(body) - 1);
};
/** Whether this process is a control process of the pool. */
const serving: boolean = process.argv[2] === "--controls";

/** A Node process of this run beside the suite's own work: its status and
 * output. It writes under this run's root, which outlives it. */
const beside = (module: string, args: readonly string[]): Promise<{ status: number | null; stdout: string; stderr: string }> =>
  new Promise((done, fail) => {
    runRoot();
    const child = spawn(process.execPath, [join(here, "..", module), ...args], { stdio: ["ignore", "pipe", "pipe"] });
    let stdout = "", stderr = "";
    child.stdout.setEncoding("utf8");
    child.stderr.setEncoding("utf8");
    child.stdout.on("data", (text: unknown) => { stdout += String(text); });
    child.stderr.on("data", (text: unknown) => { stderr += String(text); });
    child.on("error", fail);
    child.on("close", (status: number | null) => done({ status, stdout, stderr }));
  });
// The observed stages' replay controls (tests/observed-stages.mts) run their
// stages in fresh processes, the parse's with real compilers, beside the
// rest of this suite; their result is reported at its end.
const observedStages = serving ? null : beside("tests/observed-stages.mts", []);
// The retained declaration sessions' controls (tests/session-reuse.mts), in
// one process of their own beside the rest: the sessions are its own.
const sessionReuse = serving ? null : beside("tests/session-reuse.mts", []);
// The mutation verifier, built once from the current build beside the
// controls, and given to every control process.
const mutationBuild = serving ? null : beside("pipeline/evidence-mutations.mts", ["--build"]);

// Every allowed compiler enum uses the same Node binding identity check as
// family tags, including named program re-exports. TypeScript's paths read
// the audited declarations while the negative runtime exports other values.
// One control for each of a direct import and a re-export, audited and mismatched.
for (const reexport of [false, true]) for (const mismatched of [false, true]) control(async (): Promise<void> => {
  const audited = resolve(here, "../tools/node_modules/typescript");
  const dir = runDirectory("tscert-compiler-enum-binding-");
  const installed = join(dir, "node_modules", "typescript");
  mkdirSync(join(dir, "node_modules"));
  if (mismatched) {
    mkdirSync(installed);
    writeFileSync(join(installed, "package.json"), JSON.stringify({ name: "typescript", type: "module",
      exports: { "./unstable/ast": "./enums.js", "./unstable/sync": "./enums.js" } }));
    writeFileSync(join(installed, "enums.js"), hostEnums.map(({ name }) =>
      `export const ${name} = { ${name === "SyntaxKind" ? "Identifier" : name === "NodeFlags" ? "Const" : name === "TypeFlags" ? "Union" : name === "SymbolFlags" ? "Alias" : name === "SignatureKind" ? "Call" : name === "ElementFlags" ? "Required" : "Error"}: -123 };`).join("\n"));
  } else symlinkSync(audited, installed);
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
    module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
    allowImportingTsExtensions: true, paths: {
      "typescript/unstable/ast": [join(audited, "dist/ast/index.d.ts")],
      "typescript/unstable/sync": [join(audited, "dist/api/sync/api.d.ts")],
    } }, include: ["*.ts"] }));
  for (const { name } of hostEnums) {
    const member = name === "SyntaxKind" ? "Identifier" : name === "NodeFlags" ? "Const" :
      name === "TypeFlags" ? "Union" : name === "SymbolFlags" ? "Alias" :
      name === "SignatureKind" ? "Call" : name === "ElementFlags" ? "Required" : "Error";
    const entry = name === "SyntaxKind" || name === "NodeFlags" ? "ast" : "sync";
    writeFileSync(join(dir, "barrel.ts"), `export { ${name} as Enum } from "typescript/unstable/${entry}";\n`);
    const file = join(dir, "value.ts");
    writeFileSync(file, `import { ${reexport ? "Enum" : name + " as Enum"} } from "${reexport ? "./barrel.ts" : "typescript/unstable/" + entry}";\nexport function value(): Enum.${member} { return Enum.${member}; }\n`);
    const outcome = check(file, tsconfigOf(dir));
    assert.equal(outcome.status, mismatched ? "unsupported" : "verified", `${name}, reexport=${reexport}: ${JSON.stringify(outcome)}`);
    if (mismatched) {
      assert.equal(outcome.status, "unsupported");
      assert.match(outcome.detail, /the host enum/);
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { value } from ${JSON.stringify(pathToFileURL(file).href)}; console.log(value());`], { encoding: "utf8", cwd: dir });
      assert.equal(ran.status, 0, ran.stderr);
      assert.equal(ran.stdout.trim(), "-123", `${name}: Node returns the other installation's value`);
    }
  }
  process.stdout.write(`compiler enum binding, ${reexport ? "re-exported" : "direct"}: all 7 enums, ${mismatched ? "mismatched bindings refused and counterexamples executed under Node" : "audited bindings verified"}\n`);
});


function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
/** A node's sequent and derivations as the evidence wire spells them
 * (REQUEST-PROTOCOL.md, "Evidence"). */
type WireSequent = { term: unknown; context: unknown[] };
type WireDerivation = { node: { claim: WireSequent } };
type WireNode = { ordinary: "effect" | { proof: { tree: WireDerivation } } | null; sequent: WireSequent | null;
  effect: { [step: string]: { proof?: WireDerivation; [field: string]: unknown } } | null };
/** A node's sequent: its ordinary derivation's root, the sequent it states,
 * or its step's proof's root. */
function nodeSequent(node: WireNode): WireSequent {
  if (node.ordinary !== null && node.ordinary !== "effect") return node.ordinary.proof.tree.node.claim;
  if (node.sequent !== null) return node.sequent;
  const step = Object.values(must(node.effect, "a node without a derivation has step evidence"))[0];
  return must(step?.proof, "a node without a stated sequent has a step proof").node.claim;
}
/** A JSON value, as a document's text parses. */
type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };
type JsonObject = { [key: string]: JsonValue };
/** A parsed document as a JSON value, a copy of its own. */
function jsonValue(v: unknown): JsonValue {
  if (v === null || typeof v === "boolean" || typeof v === "number" || typeof v === "string") return v;
  if (Array.isArray(v)) return v.map(jsonValue);
  assert.ok(typeof v === "object", "a JSON value");
  return Object.fromEntries(Object.entries(v).map(([k, w]) => [k, jsonValue(w)]));
}
const jsonObject = (v: JsonValue | undefined): JsonObject => {
  assert.ok(typeof v === "object" && v !== null && !Array.isArray(v), "a JSON object");
  return v;
};
const jsonArray = (v: JsonValue | undefined): JsonValue[] => {
  assert.ok(Array.isArray(v), "a JSON array");
  return v;
};
const jsonIndex = (v: JsonValue | undefined): number => {
  assert.ok(typeof v === "number" && Number.isInteger(v) && v >= 0, "a reference");
  return v;
};
/** The kinds of an evidence bundle's tables, in the order each names only
 * the ones before it (REQUEST-PROTOCOL.md, "Evidence document"). */
const evidenceTables = ["types", "contexts", "links", "separations", "knowledge", "proofs"] as const;
/** Every bundle of an evidence document: the main one, then each module's. */
const evidenceBundles = (document: JsonValue): JsonObject[] => [jsonObject(jsonObject(document).main),
  ...jsonArray(jsonObject(document).modules).map((m) => jsonObject(jsonObject(m).evidence))];
/** An evidence document with every reference unfolded: each bundle spelled
 * as the responses and obligations the tables stand for, every occurrence
 * a copy of its own, for a control to edit one occurrence. */
function unfoldedEvidence(path: string): JsonValue {
  const parsed: unknown = JSON.parse(readFileSync(path, "utf8"));
  const document = jsonValue(parsed);
  for (const b of evidenceBundles(document)) {
    const at = (table: JsonValue[], k: JsonValue | undefined): JsonValue =>
      structuredClone(must(table[jsonIndex(k)], "an entry of its table"));
    const types = jsonArray(b.types), links = jsonArray(b.links), separations = jsonArray(b.separations);
    const contexts = jsonArray(b.contexts).map((c) => jsonArray(c).map((t) => at(types, t)));
    const knowledge = jsonArray(b.knowledge).map((k): JsonValue => {
      const e = jsonObject(k);
      return { cells: e.cells ?? null, values: e.values ?? null, links: jsonArray(e.links).map((l) => at(links, l)),
        separation: { depth: e.depth ?? null, facts: jsonArray(e.separation).map((a) => at(separations, a)) } };
    });
    const sequent = (s: JsonValue): JsonValue => {
      const e = jsonObject(s);
      return { context: at(contexts, e.context), term: e.term ?? null, type: at(types, e.type) };
    };
    const proofs: JsonValue[] = [];
    for (const p of jsonArray(b.proofs)) {
      const e = jsonObject(p);
      proofs.push({ node: { claim: sequent(e.claim ?? null), rule: e.rule ?? null,
        premises: jsonArray(e.premises).map((q) => at(proofs, q)) } });
    }
    const step = (s: JsonValue): JsonValue => {
      if (s === null) return null;
      const [[name, fields]] = Object.entries(jsonObject(s));
      const f = jsonObject(fields);
      return { [name]: "proof" in f ? { ...f, proof: at(proofs, f.proof) } : f };
    };
    const node = (n: JsonValue): JsonValue => {
      const e = jsonObject(n);
      const ordinary = e.ordinary ?? null;
      return { ...e, ordinary: typeof ordinary === "object" && ordinary !== null && !Array.isArray(ordinary)
          ? { proof: { tree: at(proofs, jsonObject(ordinary.proof).tree) } } : ordinary,
        sequent: e.sequent === null ? null : sequent(e.sequent ?? null), knowledge: at(knowledge, e.knowledge),
        effect: step(e.effect ?? null), output: at(knowledge, e.output) };
    };
    b.functions = jsonArray(b.functions).map((f) => {
      const r = jsonObject(f);
      return { ...r, certificate: jsonArray(r.certificate).map(node),
        ...("codes" in r ? { codes: jsonArray(r.codes).map((c) => jsonArray(c).map(node)) } : {}) };
    });
    b.obligations = jsonArray(b.obligations).map((o) => jsonArray(o).map((p) => at(proofs, p)));
    for (const table of evidenceTables) delete b[table];
  }
  return document;
}
/** A JSON value's text. */
function jsonText(v: JsonValue): string {
  const text = JSON.stringify(v);
  assert.ok(typeof text === "string", "a JSON value has a text");
  return text;
}
/** An unfolded evidence document written with tables again, each entry once:
 * the text the verifier reads. */
function tabledEvidence(document: unknown): string {
  const copy = jsonValue(document);
  for (const b of evidenceBundles(copy)) {
    const tables = new Map<string, { keys: Map<string, number>; entries: JsonValue[] }>(
      evidenceTables.map((t) => [t, { keys: new Map(), entries: [] }]));
    const add = (table: string, value: JsonValue): number => {
      const t = must(tables.get(table), table);
      const key = jsonText(value);
      const known = t.keys.get(key);
      if (known !== undefined) return known;
      t.keys.set(key, t.entries.length);
      t.entries.push(value);
      return t.entries.length - 1;
    };
    const type = (t: JsonValue | undefined): number => add("types", t ?? null);
    const sequent = (s: JsonValue | undefined): JsonValue => {
      const e = jsonObject(s);
      return { context: add("contexts", jsonArray(e.context).map(type)), term: e.term ?? null, type: type(e.type) };
    };
    const proof = (p: JsonValue | undefined): number => {
      const e = jsonObject(jsonObject(p).node);
      const premises = jsonArray(e.premises).map(proof);
      return add("proofs", { claim: sequent(e.claim), rule: e.rule ?? null, premises });
    };
    const knowledge = (k: JsonValue | undefined): number => {
      const e = jsonObject(k);
      const separation = jsonObject(e.separation);
      return add("knowledge", { cells: e.cells ?? null, values: e.values ?? null,
        links: jsonArray(e.links).map((l) => add("links", l)), depth: separation.depth ?? null,
        separation: jsonArray(separation.facts).map((a) => add("separations", a)) });
    };
    const node = (n: JsonValue): JsonValue => {
      const e = jsonObject(n);
      const ordinary = e.ordinary ?? null;
      const effect = e.effect ?? null;
      let step: JsonValue = null;
      if (effect !== null) {
        const [[name, fields]] = Object.entries(jsonObject(effect));
        const f = jsonObject(fields);
        step = { [name]: "proof" in f ? { ...f, proof: proof(f.proof) } : f };
      }
      return { ...e, ordinary: typeof ordinary === "object" && ordinary !== null && !Array.isArray(ordinary)
          ? { proof: { tree: proof(jsonObject(ordinary.proof).tree) } } : ordinary,
        sequent: e.sequent === null ? null : sequent(e.sequent), knowledge: knowledge(e.knowledge), effect: step,
        output: knowledge(e.output) };
    };
    b.functions = jsonArray(b.functions).map((f) => {
      const r = jsonObject(f);
      return { ...r, certificate: jsonArray(r.certificate).map(node),
        ...("codes" in r ? { codes: jsonArray(r.codes).map((c) => jsonArray(c).map(node)) } : {}) };
    });
    b.obligations = jsonArray(b.obligations).map((o) => jsonArray(o).map(proof));
    for (const table of evidenceTables) b[table] = must(tables.get(table), table).entries;
  }
  return jsonText(copy);
}
/** Check `claims` against `evidence` with the verifier's acceptance entry, and
 * require a refusal; its words, for the caller to match. */
const invoke = (claims: string, evidence: string, artifacts: string,
  ast: string = join(artifacts, "fragment.json")): string => {
  const p = tested(verifierCall(verifier, ["--check-source-claims", ast, claims, sourceKey(artifacts), evidence]));
  assert.ifError(p.error);
  assert.equal(p.signal, null);
  assert.equal(p.status, 1, p.stdout + p.stderr);
  return p.stdout + p.stderr;
};
/** Search for evidence of forged claims, or of a forged parser document. */
const produceWith = (artifacts: string, claims: string, name: string,
    fragmentPath: string = join(artifacts, "fragment.json")): Invoked =>
  tested(verifierCall(verifier, ["--produce-source-claims", fragmentPath, claims, sourceKey(artifacts),
    join(artifacts, `${name}-evidence.json`), "12"]));
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
const readClaims = (artifacts: string): SourceClaims => readClaimsFile(join(artifacts, "claims.json"));
/** Write forged claims beside a run's artifacts. */
const writeClaims = (artifacts: string, name: string, claims: SourceClaims): string => {
  const path = join(artifacts, `${name}.json`);
  writeFileSync(path, JSON.stringify(claims));
  return path;
};

/** The artifacts of a case's run through the pipeline (its stages replayed
 * where the store holds them), its outcome the case's expected one: one run
 * per case in a control process, its own to write beside. */
const caseRuns = new Map<string, string>();
const run = (file: string): string => {
  const held = caseRuns.get(file);
  if (held !== undefined) return held;
  const test = must(cases.find((c) => c.file === file), `case ${file}`);
  const outcome = check(join(here, "examples", `${file}.ts`),
    test.project ? tsconfigOf(resolve(here, "..", test.project)) : undefined, test.typescriptErrors);
  const { artifacts } = expectOutcome(test, outcome);
  caseRuns.set(file, artifacts);
  return artifacts;
};

control(async (): Promise<void> => {
  // A producer normally gives each array alternative its own label. One
  // label containing both clauses reaches the read's derivation refusal.
  const artifacts = run("length-array-or-record");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const start = source.indexOf("x.length");
  const fn = must(claims.functions.find(f => f.name === "size"), "size's claims");
  const receiver = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 1),
    "the length read's receiver");
  const row: Row = ["num", "str"].map(atom => {
    assert.ok(atom === "num" || atom === "str");
    const store = rowOf(claims, { list: { first: { required: [], optional: [],
      rest: [rowOf(claims, atom)], readonly: true, presence: "readable" }, rest: [] } });
    return { refs: { first: [], rest: [], views: [["[]", [store]]] } };
  });
  receiver.type = [claims.types.push(row) - 1];
  const forged = writeClaims(artifacts, "forged-grouped-array-length", claims);
  const at = `source refusal at [${start},${start + "x.length".length}): a read of \`length\` of a union some member of which is not one array contract`;
  refusedAt(artifacts, forged, "forged-grouped-array-length", at);
  assert.ok(invoke(forged, join(artifacts, "evidence.json"), artifacts).includes(at));
  process.stdout.write("grouped array length claim: refused at the member access in search and check\n");
});

control(async (): Promise<void> => {
  const good = run("values");
  // Output rebinding preserves the verifier's refusal of aliases to either
  // input, and leaves those input bytes intact.
  for (const name of ["fragment.json", "claims.json"]) {
    const input = join(good, name);
    const before = readFileSync(input);
    const result = tested(verifierCall(verifier, ["--produce-source-claims",
      join(good, "fragment.json"), join(good, "claims.json"), sourceKey(good), input, "12"]));
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.ok(result.record.execution === "executed" || result.record.execution === "replayed", result.record.execution);
    assert.match(result.stdout + result.stderr, /evidence output must differ from the input files/);
    assert.deepEqual(readFileSync(input), before);
  }
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
});

control(async (): Promise<void> => {
  // Bypass the producer's refusal: manufacture its old proposal by erasing
  // the method in a copy of the AST. Both verifier entry points must still
  // refuse the ORIGINAL contract before accepting any such proposal/evidence.
  const erased = run("invalid-generic-contract-erasure");
  const ast: Ast = readFragmentFile(join(erased, "fragment.json"));
  const declaration = ast.declarations?.definitions.find(d => d.declaration.name === "Witness");
  assert(declaration?.expression?.k === "object");
  const member = declaration.expression.fields.find(f => f.name === "choose");
  assert(member?.type.k === "scheme");
  member.type = { k: "atom", name: "unknown", span: member.type.span };
  const weakened = join(erased, "weakened.json");
  writeFileSync(weakened, JSON.stringify(ast));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", weakened]));
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(erased, "weakened-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposal = tested(producerCall(producerExecutable, [weakened, flow]));
  assert.equal(proposal.status, 0, proposal.stderr);
  const claims = join(erased, "forged-claims.json");
  const evidence = join(erased, "forged-evidence.json");
  writeFileSync(claims, proposal.stdout);
  writeFileSync(evidence, "{}");
  const searched = tested(verifierCall(verifier, ["--produce-source-claims",
    join(erased, "fragment.json"), claims, sourceKey(erased), evidence, "12"]));
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /generic contract.*cannot be erased/);
  assert.match(invoke(claims, evidence, erased), /generic contract.*cannot be erased/);
});
control(async (): Promise<void> => {
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
    const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
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
    const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
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
            "reference" in value && (JSON.stringify(value.reference) ?? "").includes('"name":"Keys"')) found.push(value.args);
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
});
control(async (): Promise<void> => {
  // `Symbol.toStringTag` is the native `Promise` contract's: the declaration
  // document lists it by its identity, only that contract's prototype holds
  // it, its `then` names no `PromiseLike`, and no object the source makes is
  // keyed by it. A document tampered with in any of these is refused where
  // evidence is produced and where it is checked.
  const tagged = (good: string, name: string, edit: (ast: Ast) => string, refusal: RegExp,
      claims: string = join(good, "claims.json"), checked: RegExp = refusal,
      evidence: string = join(good, "evidence.json")): void => {
    const path = join(good, `${name}.fragment.json`);
    writeFileSync(path, edit(readFragmentFile(join(good, "fragment.json"))));
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const result = tested(verifierCall(verifier, [mode, path, claims, sourceKey(good),
        mode === "--produce-source-claims" ? join(good, `${name}-evidence.json`) : evidence,
        ...(mode === "--produce-source-claims" ? ["12"] : [])]));
      assert.ifError(result.error);
      assert.equal(result.status, 1, result.stdout + result.stderr);
      assert.match(result.stdout + result.stderr, mode === "--produce-source-claims" ? refusal : checked);
    }
  };
  const wellKnown = '"module":"typescript/lib/lib.es2015.symbol.wellknown.d.ts","name":"toStringTag"';
  const promises = run("async-await");
  const native = (ast: Ast) => must(ast.declarations.definitions.find(d =>
    d.declaration.name === "Promise" && d.declaration.module.startsWith("typescript/lib/")), "the native Promise");
  const untagged = /the native Promise contract states no readonly `Symbol.toStringTag` of type string/;
  tagged(promises, "tag-renamed", ast => {
    const text = JSON.stringify(ast);
    assert.ok(text.includes(wellKnown), "the tag's listed identity");
    return text.replace(wellKnown, wellKnown.replace('"toStringTag"', '"toStringTagX"'));
  }, untagged);
  tagged(promises, "tag-dropped", ast => {
    const index = ast.declarations.symbols.findIndex(s => JSON.stringify(s).includes(wellKnown));
    const text = JSON.stringify(native(ast));
    assert.ok(index >= 0 && text.includes(`"name":{"symbol":${index}}`), "the native prototype's tag");
    return JSON.stringify(ast).replace(text, text.replaceAll(`"name":{"symbol":${index}}`, '"name":"tag"'));
  }, untagged);
  tagged(promises, "tag-promise-like", ast => {
    const text = JSON.stringify(native(ast));
    const reference = '"reference":{"name":"Promise","span"';
    assert.ok(text.includes(reference), "a Promise the native then's callbacks return");
    return JSON.stringify(ast).replace(text, text.replace(reference, '"reference":{"name":"PromiseLike","span"'));
  }, /the native Promise contract names PromiseLike/);
  const fields = run("then-member-fields");
  tagged(fields, "tag-allocation", ast => {
    const index = ast.declarations.symbols.length;
    ast.declarations.symbols.push({ module: "typescript/lib/lib.es2015.symbol.wellknown.d.ts", name: "toStringTag",
      span: [0, 0] });
    const text = JSON.stringify(ast);
    assert.ok(text.includes('{"name":"then","e":'), "an allocation's then field");
    return text.replace('{"name":"then","e":', `{"name":{"symbol":${index}},"e":`);
  }, /an object the source makes is keyed by `Symbol.toStringTag`/);
  // `Fake` given the native contract's members at `number`, its methods
  // compatible with the native ones. As an exact copy its prototype is the
  // native record, and it verifies. With the tag dropped from its prototype,
  // its value returned as a `Promise<number>` is refused at the return where
  // evidence is produced, and the exact copy's evidence, justifying the
  // return by the tag, is refused where it is checked: dropping the tag makes
  // the prototype a record of its own, a head the exact copy's store lacks,
  // so that evidence's labels name other rows and it is refused as it is
  // read. With the tag on a prototype of one more field, on Fake or on
  // a base, or on a prototype that is a callable object, the document is
  // refused in both.
  const inherited = run("tag-fake-holder");
  // The copied contract with its prototype a callable object: every
  // prototype field writable, and a call signature.
  const callablePrototype = (text: string): string => {
    const contract: unknown = JSON.parse(text);
    const prototype = contract && typeof contract === "object" && "prototype" in contract ? contract.prototype : null;
    assert.ok(prototype && typeof prototype === "object" && "fields" in prototype && Array.isArray(prototype.fields) &&
      "calls" in prototype, "the copied prototype record");
    const fields: unknown[] = prototype.fields;
    for (const field of fields) if (field && typeof field === "object" && "readonly" in field) field.readonly = false;
    prototype.calls = [{ k: "function", effect: { footprint: { value: "any", store: "any" }, promise: null, fresh: false,
      receiverStore: false, onThrow: false }, receiver: null, params: [], rest: null,
      result: { k: "atom", name: "unknown", span: [0, 0] }, span: [0, 0] }];
    return must(JSON.stringify(contract), "the callable contract's text");
  };
  type FakeMode = "exact" | "untagged" | "distinct" | "base" | "callable";
  const fakeAt = (ast: Ast, mode: FakeMode): string => {
    const promise = native(ast);
    const fake = must(ast.declarations.definitions.find(d => d.declaration.name === "Fake"), "Fake");
    const index = ast.declarations.symbols.findIndex(s => JSON.stringify(s).includes(wellKnown));
    const text = JSON.stringify(must(promise.expression, "the native contract"))
      .replace(/\{"k":"parameter","index":0,"span":\[\d+,\d+\]\}/g, '{"k":"atom","name":"number","span":[0,0]}');
    const opening = '"prototype":{"k":"object","fields":[';
    assert.ok(text.includes(opening), "the copied prototype");
    const extra = '{"name":"forged","optional":false,"readonly":true,"type":{"k":"atom","name":"unknown","span":[0,0]},"span":[0,0]},';
    const body = mode === "exact" ? text
      : mode === "untagged" ? text.replace(new RegExp(`\\{"name":\\{"symbol":${index}\\}[^}]*\\}[^}]*\\},`), "")
      : mode === "callable" ? callablePrototype(text)
        : text.replace(opening, opening + extra);
    assert.ok(mode === "exact" || body !== text, `the ${mode} copy`);
    const replaced = mode === "base"
      ? JSON.stringify({ ...fake, bases: [JSON.parse(body)] })
      : JSON.stringify({ ...fake, bases: [], expression: JSON.parse(body) });
    return JSON.stringify(ast).replace(JSON.stringify(fake), replaced);
  };
  const at = readFileSync(sourceKey(inherited), "utf8").indexOf("return f;") + "return ".length;
  {
    const exact = join(inherited, "tag-fake-exact.fragment.json");
    writeFileSync(exact, fakeAt(readFragmentFile(join(inherited, "fragment.json")), "exact"));
    const produced = tested(verifierCall(verifier, ["--produce-source-claims", exact, join(inherited, "claims.json"),
      sourceKey(inherited), join(inherited, "tag-fake-exact-evidence.json"), "12"]));
    assert.equal(produced.status, 0, produced.stdout + produced.stderr);
  }
  tagged(inherited, "tag-fake-untagged", ast => fakeAt(ast, "untagged"),
    new RegExp(`source expression obligation at \\[${at},${at + 1}\\): evidence search failed`),
    join(inherited, "claims.json"), /^reject: /, join(inherited, "tag-fake-exact-evidence.json"));
  const otherPrototype = /a prototype holding `Symbol.toStringTag` other than the native Promise's/;
  tagged(inherited, "tag-fake-tagged", ast => fakeAt(ast, "distinct"), otherPrototype);
  tagged(inherited, "tag-fake-base", ast => fakeAt(ast, "base"), otherPrototype);
  tagged(inherited, "tag-fake-callable", ast => fakeAt(ast, "callable"), /a prototype is stated as no record/);
  process.stdout.write("forged tag documents: the tag renamed, dropped, stated of another prototype or a base's, PromiseLike in the native then, an allocation keyed by the tag; a contract with the native methods and no tag, a callable prototype: refused\n");
});
control(async (): Promise<void> => {
  // A resolving operation's instance claimed at a record with a callable
  // `then` (the fixture's `thenable`) in place of its stable operand: `await`,
  // an async return and `Promise.resolve` at a resolution-qualified binder,
  // `new Promise` at its primitive-bounded one. Each is refused at the
  // operation where evidence is produced and where it is checked; so is an
  // allocation with a callable `then` claimed as a promise.
  const artifacts = run("then-member-resolution");
  for (const functionName of ["awaited", "returned", "resolved", "made"]) {
    const claims = readClaims(artifacts);
    const thenable = claims.types.findIndex(row => JSON.stringify(row).startsWith('[{"refs":{"first":[["then",'));
    assert.ok(thenable >= 0, "the thenable's row");
    const fn = must(claims.functions.find(f => f.name === functionName), `${functionName}'s claims`);
    const site = must(fn.expressions.find(e => e.instantiate?.length), "the resolving operation's instance");
    for (const image of site.instantiate ?? []) image.type = [thenable];
    const name = `forged-thenable-${functionName}`;
    const forged = writeClaims(artifacts, name, claims);
    const at = `at [${site.pos[0]},${site.pos[1]})`;
    const searched = produceWith(artifacts, forged, name);
    const detail = searched.stdout + searched.stderr;
    assert.equal(searched.status, 1, detail);
    assert.ok(detail.includes(at), detail);
    const checked = invoke(forged, join(artifacts, "evidence.json"), artifacts);
    assert.ok(checked.includes(at), checked);
  }
  {
    // `local`'s allocation, a record with a callable `then`, claimed as the
    // `Promise<number>` `returned`'s result is claimed at.
    const claims = readClaims(artifacts);
    const source = readFileSync(sourceKey(artifacts), "utf8");
    const start = source.indexOf("{ then: (x: number): number => x + 1 }");
    const fn = must(claims.functions.find(f => f.name === "local"), "local's claims");
    const allocation = must(fn.expressions.find(e => e.pos[0] === start), "the allocation's claim");
    allocation.type = must(claims.functions.find(f => f.name === "returned"), "returned's claims").result;
    const forged = writeClaims(artifacts, "forged-thenable-allocation", claims);
    const at = `at [${allocation.pos[0]},${allocation.pos[1]})`;
    const searched = produceWith(artifacts, forged, "forged-thenable-allocation");
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.ok((searched.stdout + searched.stderr).includes(at), searched.stdout + searched.stderr);
    // The evidence for the allocation's own claim does not justify the
    // forged one, at the allocation.
    const checked = invoke(forged, join(artifacts, "evidence.json"), artifacts);
    assert.ok(checked.includes(`source evidence refusal ${at}`), checked);
  }
  process.stdout.write("forged thenable instances: await, async return, Promise.resolve and new Promise at a callable then, and an allocation claimed as a promise, refused\n");
});
control(async (): Promise<void> => {
  // A key-adding write's key claimed at `symbol` in place of `string`: it
  // may be `Symbol.toStringTag`, which no object the program makes holds, so
  // the write is refused where evidence is produced; checking refuses the
  // evidence of the original claim for it.
  const growth = run("tag-key-growth");
  const claims = readClaims(growth);
  const source = readFileSync(sourceKey(growth), "utf8");
  const start = source.indexOf("d[k] = 1") + "d[".length;
  const fn = must(claims.functions.find(f => f.name === "grown"), "grown's claims");
  const key = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 1), "the key's claim");
  key.type = [rowOf(claims, "symbol")];
  const forged = writeClaims(growth, "forged-tag-key", claims);
  const write = source.indexOf("d[k] = 1");
  refusedAt(growth, forged, "forged-tag-key",
    `source refusal at [${write},${write + "d[k] = 1".length}): a key-adding write at a key that may be \`Symbol.toStringTag\``);
  invoke(forged, join(growth, "evidence.json"), growth);
  process.stdout.write("forged tag key: a key-adding write claimed at a symbol key refused\n");
});
control(async (): Promise<void> => {
  // A computed key's expression is checked at the literal its field's key
  // spells: with the read of `awaitName` claimed at another literal, the key
  // is refused where evidence is produced, and checking refuses the evidence of
  // the original claim for it.
  const keyed = run("object-computed-literal-key");
  const claims = readClaims(keyed);
  const source = readFileSync(sourceKey(keyed), "utf8");
  const start = source.indexOf("[awaitName]: 0") + 1;
  const fn = must(claims.functions.find(f => f.name === "names"), "names' claims");
  const read = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + "awaitName".length),
    "the key's read");
  read.type = [rowOf(claims, { strLit: { value: "k" } })];
  const forged = writeClaims(keyed, "forged-computed-key", claims);
  const searched = produceWith(keyed, forged, "forged-computed-key");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  // Refused at the key, `[awaitName]`, checked at its literal.
  assert.ok((searched.stdout + searched.stderr).includes(`[${start - 1},${start + "awaitName".length + 1})`),
    searched.stdout + searched.stderr);
  invoke(forged, join(keyed, "evidence.json"), keyed);
  // A computed field's key is the one its checked literal converts to: with
  // the key claim unchanged, a field renamed (`"x"` for `"%Await%"`) or
  // spelled otherwise than the number's `ToString` (`"1.0"` for `1`) is
  // refused where evidence is produced and where it is checked.
  for (const [name, from, to] of [["computed-key-renamed", '"%Await%"', '"x"'],
      ["computed-key-numeric", '"1"', '"1.0"']] as const) {
    const text = readFileSync(join(keyed, "fragment.json"), "utf8");
    const field = `{"name":${from},"e":{"k":"comma"`;
    assert.ok(text.includes(field), `the computed field ${from}`);
    const path = join(keyed, `${name}.fragment.json`);
    writeFileSync(path, text.replace(field, `{"name":${to},"e":{"k":"comma"`));
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const result = tested(verifierCall(verifier, [mode, path, join(keyed, "claims.json"), sourceKey(keyed),
        join(keyed, mode === "--produce-source-claims" ? `${name}-evidence.json` : "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : [])]));
      assert.equal(result.status, 1, result.stdout + result.stderr);
      assert.match(result.stdout + result.stderr, /is not the key .* its literal converts to/);
    }
  }
  process.stdout.write("forged computed key: a key's read claimed at another literal, a field renamed or spelled otherwise than its number's ToString: refused\n");
});
control(async (): Promise<void> => {
  // An `Error`-derived instance holds its message on its first link, and no
  // `stack`: `new Decline()` claimed at a record owning `message`, or
  // holding `stack` beside it, is refused where evidence is produced, and
  // checking refuses the evidence of the original claim for it.
  const errors = run("error-subclass");
  const source = readFileSync(sourceKey(errors), "utf8");
  const start = source.indexOf("new Decline()");
  const at = `[${start},${start + "new Decline()".length})`;
  const forgeries: [name: string, owned: string[], viewed: string[]][] = [
    ["forged-error-own-message", ["message"], []],
    ["forged-error-stack", [], ["message", "stack"]],
  ];
  for (const [name, owned, viewed] of forgeries) {
    const claims = readClaims(errors);
    const str = rowOf(claims, "str");
    const fields = (names: string[]): [string, number[]][] => names.map((field) => [field, [str]]);
    const fn = must(claims.functions.find((f) => f.name === "omitted"), "omitted's claims");
    const made = must(fn.expressions.find((e) => e.pos[0] === start && e.pos[1] === start + "new Decline()".length),
      "the construction's claim");
    made.type = [rowOf(claims, { refs: { first: fields(owned), rest: [], views: fields(viewed) } })];
    const forged = writeClaims(errors, name, claims);
    refusedAt(errors, forged, name, at);
    invoke(forged, join(errors, "evidence.json"), errors);
  }
  process.stdout.write("forged error instances: an own message and a stack claimed of a constructed error, refused\n");
});
control(async (): Promise<void> => {
  // A pattern binding a `for...of` over a program's iterable reads the
  // step's value through a name no source spells, at the head's `const `:
  // claiming that read, or the step's value it binds, at a string is
  // refused where evidence is produced and where it is checked.
  const patterns = run("for-of-pattern-program-iterable");
  const source = readFileSync(sourceKey(patterns), "utf8");
  const head = source.indexOf("const [key, n] of pairs");
  const pattern = head + "const ".length;
  // A string where the pattern reads the pair is refused where the pattern
  // binds; one where the step's value is bound, at that read.
  const key = source.indexOf("key", pattern);
  const sites: [name: string, pos: [number, number], at: string][] = [
    ["forged-for-of-element-read", [head, pattern],
      `at [${key},${key + "key".length}): an array pattern requires an array contract`],
    ["forged-for-of-element-value", [pattern, pattern + "[key, n]".length],
      `at [${pattern},${pattern + "[key, n]".length})`],
  ];
  for (const [name, pos, at] of sites) {
    const claims = readClaims(patterns);
    const fn = must(claims.functions.find((f) => f.name === "keyed"), "keyed's claims");
    must(fn.expressions.find((e) => e.pos[0] === pos[0] && e.pos[1] === pos[1]), `the claim at [${pos}]`).type =
      [rowOf(claims, "str")];
    const forged = writeClaims(patterns, name, claims);
    refusedAt(patterns, forged, name, at);
    invoke(forged, join(patterns, "evidence.json"), patterns);
  }
  process.stdout.write("forged for-of patterns: the element's read and the step's value claimed at a string, refused\n");
});
control(async (): Promise<void> => {
  // The allocation route's trusted boundary: the parser reserves `message`
  // and `stack` as member names of a class extending `Error` (SOURCE-ELABORATION.md, "A class
  // extending Error"), and Lean reads no class declaration. A fragment, claims
  // and evidence with `text` renamed `stack` throughout are accepted: the
  // reservation is the parser's alone.
  const methods = run("error-subclass-methods");
  const renamed = (file: string): string => {
    const path = join(methods, `forged-stack-member-${file}`);
    writeFileSync(path, readFileSync(join(methods, file), "utf8").replaceAll('"text"', '"stack"')
      .replaceAll("Located.text", "Located.stack"));
    return path;
  };
  const fragment = renamed("fragment.json");
  const accepted = tested(verifierCall(verifier, ["--check-source-claims", fragment, renamed("claims.json"),
    sourceKey(methods), renamed("evidence.json")]));
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  assert.ok(readFileSync(fragment, "utf8").includes('"name":"stack"'), "the forged fragment names a member `stack`");
  process.stdout.write("forged stack member: accepted by Lean, the reservation enforced by the parser alone\n");
});
control(async (): Promise<void> => {
  // The write route is Lean's: each write of `reserved-write-twin`, its key
  // renamed `stack` in the fragment, the claims and the evidence, is a valid,
  // otherwise typable document the reserved-write check alone refuses, at
  // the write, where evidence is produced and where it is checked.
  const twin = run("reserved-write-twin");
  const source = readFileSync(sourceKey(twin), "utf8");
  for (const [key, write] of [["stackPattern", "o.stackPattern"], ["stackUpdate", 'o.stackUpdate += "s"'],
      ["stackLogical", 'o.stackLogical ??= "s"'], ["stackCallback", "o.stackCallback = v"], ["stackComputed", 'o[k] = "s"']] as const) {
    const renamed = (file: string): string => {
      const path = join(twin, `forged-${key}-${file}`);
      writeFileSync(path, readFileSync(join(twin, file), "utf8").replaceAll(`"${key}"`, '"stack"'));
      return path;
    };
    const fragment = renamed("fragment.json");
    const claims = renamed("claims.json");
    const start = source.indexOf(write);
    const at = `source refusal at [${start},${start + write.length}): a write at a key that may be \`message\` or \`stack\``;
    const searched = produceWith(twin, claims, `forged-${key}`, fragment);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.ok((searched.stdout + searched.stderr).includes(at), searched.stdout + searched.stderr);
    assert.ok(invoke(claims, renamed("evidence.json"), twin, fragment).includes(at), key);
  }
  process.stdout.write("forged reserved writes: each write form renamed to `stack`, refused at the write in search and check\n");
});
control(async (): Promise<void> => {
  // An optional call of a method reads its object again as the call's
  // receiver, claimed at the method's name: claimed at `undefined`, it is
  // refused there where evidence is produced, and checking refuses the
  // evidence of the original claim for it.
  const optional = run("optional-method-call");
  const claims = readClaims(optional);
  const source = readFileSync(sourceKey(optional), "utf8");
  const start = source.indexOf("equation?.(x) ??");
  const fn = must(claims.functions.find(f => f.name === "withDefault"), "withDefault's claims");
  const receiver = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + "equation".length),
    "the receiver read again");
  receiver.type = [rowOf(claims, "undef")];
  const forged = writeClaims(optional, "forged-optional-receiver", claims);
  const searched = produceWith(optional, forged, "forged-optional-receiver");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.ok((searched.stdout + searched.stderr).includes(`[${start},${start + "equation".length})`),
    searched.stdout + searched.stderr);
  invoke(forged, join(optional, "evidence.json"), optional);
  process.stdout.write("forged optional method call: the receiver read again claimed at undefined refused\n");
});
control(async (): Promise<void> => {
  // A parameter's entry claim in an `&&` operand is its first read before a
  // call, which the incoming edge checks: a read claimed narrower than any
  // test establishes is refused where evidence is produced and where it is
  // checked.
  const good = run("logical-narrowing-past-reads");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "untested"), "untested function");
  const start = source.indexOf("Number.isSafeInteger(v);\n}\n", source.indexOf("function untested")) + "Number.isSafeInteger(".length;
  const read = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 1), "the read of v");
  read.type = [rowOf(claims, "num")];
  const forged = writeClaims(good, "untested-number", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "untested-number-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
  }
  process.stdout.write("forged operand entry: a parameter read claimed narrower than its test refused\n");
});
control(async (): Promise<void> => {
  // A chain read right-nested types its first operand where the chain
  // starts; the residual `b && c` is observed at an empty span, which names
  // no source expression. The first read of `rest` claimed without
  // `undefined`, as if the chain's later operands had answered, is refused
  // where evidence is produced and where it is checked.
  const good = run("logical-chain-entry");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "inConditional"), "inConditional function");
  const start = source.indexOf("rest && rest.kind", source.indexOf("function inConditional"));
  const read = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + "rest".length), "the first read of rest");
  const undefinedRow = rowOf(claims, "undef");
  const claimed = read.type;
  if (!Array.isArray(claimed) || !claimed.includes(undefinedRow))
    throw new Error("the first read of rest is claimed as a union with undefined");
  read.type = claimed.filter(t => t !== undefinedRow);
  const forged = writeClaims(good, "chain-entry-defined", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "chain-entry-defined-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
  }
  process.stdout.write("forged chain entry: a chain's first read claimed as if later operands had answered refused\n");
});
control(async (): Promise<void> => {
  // A call claimed at the empty type leaves a slot no value meets in its
  // statement's context, whose edge onward is then never taken
  // (`vacuous-edge`, PROGRAM-TYPING.md). The claim is the call's, checked at
  // the callee's signature: `warn`, which returns, claimed at the empty type
  // is refused where evidence is produced and where it is checked.
  const good = run("never-call-narrowing");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "warned"), "warned function");
  const call = 'warn("not a string")';
  const start = source.indexOf(call, source.indexOf("function warned"));
  const claim = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + call.length), "the call of warn");
  claim.type = [];
  const forged = writeClaims(good, "never-call", claims);
  refusedAt(good, forged, "never-call", `at [${start},${start + call.length})`);
  invoke(forged, join(good, "evidence.json"), good);
  process.stdout.write("forged never call: a call of a function that returns claimed at the empty type refused\n");
});
control(async (): Promise<void> => {
  // A family guard is the inline membership test of a name only where no
  // write in its binding's scope names it (`unassigned`): a nested closure's
  // write keeps the guard an ordinary call; another function's write of its
  // own `e` does not.
  const lowered = (file: string): boolean =>
    readFileSync(join(run(file), "fragment.json"), "utf8").includes('"tagMember"');
  assert.ok(lowered("compiler-api-guard-own-binding"),
    "compiler-api-guard-own-binding: the guard of a never-assigned binding is not the membership test");
  assert.ok(!lowered("compiler-api-guard-closure-write"),
    "compiler-api-guard-closure-write: the guard of a binding a closure assigns is the membership test");
  process.stdout.write("guard binding: a closure's write keeps the guard an ordinary call, another binding's does not\n");
});
control(async (): Promise<void> => {
  // A guard that can hold of its actual leaves its `true` branch reachable:
  // the promise filtered by the slot's type keeps the promise's labels
  // (`fact-filter`, PROGRAM-TYPING.md), so the branch's value forged at a
  // string is refused where evidence is produced and where it is checked.
  const good = run("compiler-api-guard-closure-write");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "f"), "f");
  const arm = source.indexOf("? 0 : 1") + 2;
  const claim = must(fn.expressions.find(e => e.pos[0] === arm && e.pos[1] === arm + 1), "the true branch's value");
  claim.type = [rowOf(claims, "str")];
  const forged = writeClaims(good, "guard-live-branch", claims);
  refusedAt(good, forged, "guard-live-branch", "evidence search failed");
  invoke(forged, join(good, "evidence.json"), good);
  process.stdout.write("forged guard branch: a branch a guard that can hold leaves reachable is checked\n");
});
control(async (): Promise<void> => {
  // A contextual closure parameter's record is the parser's reading of its
  // context. The closure's claim must stay within it: claimed at the record
  // without its field, with the field at another type, or with an optional
  // field present where the record admits it absent only (`v?: never`), it
  // is refused at the closure. A claim within it, at a record with a field
  // added or an optional field made required, is a narrower domain the
  // closure may take, and is refused where `map` is offered it at the
  // broader one. Each is refused where evidence is produced, and where it is
  // checked: outside the record at the closure as in search, within it at
  // the closure, whose evidence establishes the original claim only. The
  // check controls establish that evidence for the original claim does not
  // check the forged one; they do not check `map`'s application of a
  // narrower closure given valid evidence for it. Each forged document is the claims with the closure's parameter at
  // another record row the claims carry (the fixture's `forgedAt` states
  // them), so its rows and the evidence's labels are unchanged.
  const forge = (good: string, name: string, record: string, forged: string, at: string,
      checkedAt: string = at): void => {
    const claims = readClaims(good);
    const rows = claims.types.map(row => JSON.stringify(row));
    const index = rows.indexOf(record);
    const target = rows.indexOf(forged);
    assert.ok(index >= 0 && target >= 0, "the parameter's record row and the forged one");
    const arrow = rows.findIndex(r => r.includes(`"arguments":[[${index}],`));
    assert.ok(arrow >= 0, "the closure's arrow row");
    const path = join(good, `${name}.json`);
    writeFileSync(path, JSON.stringify(claims).replace(rows[arrow] ?? "", (rows[arrow] ?? "")
      .replace(`"arguments":[[${index}],`, `"arguments":[[${target}],`)));
    refusedAt(good, path, name, at);
    const checked = invoke(path, join(good, "evidence.json"), good);
    assert.ok(checked.includes(checkedAt), checked);
  };
  const outside = "closure signature claim is outside the source annotation";
  const records = run("closure-contextual-records");
  const text = readFileSync(sourceKey(records), "utf8");
  const closure = text.indexOf("(o) => o.a");
  const atClosure = `at [${closure},${closure + "(o) => o.a".length}): ${outside}`;
  const map = text.indexOf("pairs.map");
  const offered = `obligation at [${map},${map + "pairs.map".length}): evidence search failed`;
  const unestablished = `at [${closure},${closure + "(o) => o.a".length}): the evidence does not establish this obligation's claim`;
  const pairRow = (rows: { str: number; num: number }, first: string, b: string) =>
    `[{"refs":{"first":${first},"rest":[],"views":${b === "view" ? `[["b",[${rows.str}]]]` : "[]"}` +
    (b === "view" ? "" : `,"optional":[{"key":"b","readonly":true,"type":[${rows.str}]}]`) + "}}]";
  const labels = { str: rowOf(readClaims(records), "str"), num: rowOf(readClaims(records), "num") };
  const pair = pairRow(labels, `[["a",[${labels.num}]]]`, "optional");
  forge(records, "contextual-record-dropped-field", pair, pairRow(labels, "[]", "optional"), atClosure);
  forge(records, "contextual-record-narrowed-field", pair, pairRow(labels, `[["a",[${labels.str}]]]`, "optional"), atClosure);
  forge(records, "contextual-record-added-field", pair,
    pairRow(labels, `[["a",[${labels.num}]],["c",[${labels.num}]]]`, "optional"), offered, unestablished);
  forge(records, "contextual-record-optional-required", pair, pairRow(labels, `[["a",[${labels.num}]]]`, "view"), offered,
    unestablished);
  // `absent`'s parameter, `Box<never>` (`v` absent only), claimed at
  // `Box<undefined>`: the arrow's parameter names the declaration at
  // another argument, so the claims keep their rows.
  const instances = run("closure-contextual-optional-instances");
  const source = readFileSync(sourceKey(instances), "utf8");
  const absent = source.indexOf("(b) => b.v", source.indexOf("Box<never>"));
  const atAbsent = `at [${absent},${absent + "(b) => b.v".length}): ${outside}`;
  {
    const claims = readClaims(instances);
    const text = JSON.stringify(claims);
    const never = /"arguments":\[\[\{"decl":(\d+),"args":\[\[\]\]\}\],/.exec(text);
    assert.ok(never, "the closure's parameter at Box<never>");
    const path = join(instances, "contextual-record-absent-present.json");
    writeFileSync(path, text.replace(never[0],
      `"arguments":[[{"decl":${never[1]},"args":[[${rowOf(claims, "undef")}]]}],`));
    refusedAt(instances, path, "contextual-record-absent-present", atAbsent);
    const checked = invoke(path, join(instances, "evidence.json"), instances);
    assert.ok(checked.includes(atAbsent), checked);
  }
  process.stdout.write("forged contextual records: a closure claimed outside its record (`Box<never>` at `Box<undefined>` included) refused at the closure, within it refused where map takes it (search) or at its closure's evidence (check)\n");
});
control(async (): Promise<void> => {
  // An early binding's cell, its marker and its checked accesses are the
  // lowering's, from the source: claims can neither drop the binding's
  // contract, nor narrow it below its annotation, nor claim a checked
  // access past the contract where nothing establishes the contents. Each
  // forged claim is refused where evidence is produced and where it is
  // checked.
  const good = run("early-bindings");
  const source = readFileSync(sourceKey(good), "utf8");
  const forge = (name: string, edit: (fn: SourceClaims["functions"][number], claims: SourceClaims) => void,
      at: string): void => {
    const claims = readClaims(good);
    edit(must(claims.functions.find(f => f.name === "later"), "later"), claims);
    const forged = writeClaims(good, name, claims);
    refusedAt(good, forged, name, at);
    invoke(forged, join(good, "evidence.json"), good);
  };
  forge("early-no-contract", fn => { fn.contracts = fn.contracts.filter(c => c.name !== "n"); },
    "no claimed storage contract for the early binding 'n'");
  forge("early-narrow-contract", (fn, claims) => {
    for (const c of fn.contracts) if (c.name === "n") c.type = [rowOf(claims, { numLit: { bits: "4607182418800017408" } })];
  }, "claimed storage contract differs from the source annotation for 'n'");
  const read = source.indexOf("=> n;", source.indexOf("function later")) + "=> ".length;
  forge("early-narrow-read", (fn, claims) => {
    const e = must(fn.expressions.find(x => x.pos[0] === read && x.pos[1] === read + 1), "the read of n");
    e.type = [rowOf(claims, { numLit: { bits: "4611686018427387904" } })];
  }, `at [${read},${read + 1})`);
  // An unannotated early binding's contract is its function literal's
  // annotations: `wanted`'s claimed at a string is refused.
  {
    const claims = readClaims(good);
    const fn = must(claims.functions.find(f => f.name === "count"), "count");
    const c = must(fn.contracts.find(x => x.name === "wanted"), "wanted's contract");
    c.type = [rowOf(claims, "str")];
    const path = writeClaims(good, "early-literal-contract", claims);
    refusedAt(good, path, "early-literal-contract", "the early binding 'wanted' needs its type stated");
    invoke(path, join(good, "evidence.json"), good);
  }
  // A property spelled as a later constant is no mention: the file lists no
  // `%ThrowUninitialized%`.
  assert.ok(!readFileSync(join(run("early-property-spelling"), "fragment.json"), "utf8").includes("%ThrowUninitialized%"),
    "early-property-spelling: the intrinsic listed without an early binding");
  // A module cell's one contract is the initialization unit's: dropped, the
  // initialization and every unit reading the cell are refused; narrowed
  // below the annotation, refused.
  {
    const cells = run("module-cells");
    const claims = readClaims(cells);
    const init = must(claims.init, "module-cells' initialization claims");
    init.contracts = init.contracts.filter(c => c.name !== "count");
    const path = writeClaims(cells, "module-cell-no-contract", claims);
    refusedAt(cells, path, "module-cell-no-contract", "count");
    invoke(path, join(cells, "evidence.json"), cells);
    const narrowed = readClaims(cells);
    const ninit = must(narrowed.init, "module-cells' initialization claims");
    for (const c of ninit.contracts) if (c.name === "count") c.type = [rowOf(narrowed, { numLit: { bits: "0" } })];
    const npath = writeClaims(cells, "module-cell-narrow-contract", narrowed);
    refusedAt(cells, npath, "module-cell-narrow-contract", "claimed storage contract differs from the source annotation for 'count'");
    invoke(npath, join(cells, "evidence.json"), cells);
    // A unit's entry knows nothing of a module cell's contents, and a call
    // may write it: a narrower entry claim, or a read after the call claimed
    // at the value written before it, is refused.
    const entry = readClaims(cells);
    const after = must(entry.functions.find(f => f.name === "afterCall"), "afterCall");
    const first = must(after.entries.reduce<(typeof after.entries)[number] | undefined>(
      (a, e) => (!a || e.start < a.start ? e : a), undefined), "afterCall's entry");
    for (const b of first.bindings) if (b.name === "count") b.type = [rowOf(entry, { numLit: { bits: "0" } })];
    const epath = writeClaims(cells, "module-cell-entry-fact", entry);
    refusedAt(cells, epath, "module-cell-entry-fact", "count");
    invoke(epath, join(cells, "evidence.json"), cells);
    const stale = readClaims(cells);
    const sfn = must(stale.functions.find(f => f.name === "afterCall"), "afterCall");
    const src = readFileSync(sourceKey(cells), "utf8");
    const at = src.indexOf("return count;", src.indexOf("function afterCall")) + "return ".length;
    const read = must(sfn.expressions.find(x => x.pos[0] === at && x.pos[1] === at + "count".length), "the read after the call");
    read.type = [rowOf(stale, { numLit: { bits: "4607182418800017408" } })];
    const spath = writeClaims(cells, "module-cell-stale-read", stale);
    refusedAt(cells, spath, "module-cell-stale-read", `at [${at},${at + "count".length})`);
    invoke(spath, join(cells, "evidence.json"), cells);
  }
  process.stdout.write("forged early bindings: a dropped or narrowed contract, a literal's contract unlike its annotations and a narrowed checked access refused; the intrinsic listed exactly\n");
});
control(async (): Promise<void> => {
  // Where `n.kind === 1 || b.kind === 2` holds, `n` may be of any arm: a
  // read of `n` claimed at the first arm is refused where evidence is
  // produced and where it is checked.
  const good = run("field-test-disjunction");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "mixed"), "mixed function");
  const start = source.indexOf("return n.kind", source.indexOf("function mixed")) + "return ".length;
  const read = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 1), "the read of n");
  assert.ok(Array.isArray(read.type) && read.type.length === 3, JSON.stringify(read.type));
  read.type = read.type.slice(0, 1);
  const forged = writeClaims(good, "disjunction-one-arm", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "disjunction-one-arm-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    if (mode === "--produce-source-claims")
      assert.match(result.stdout + result.stderr, new RegExp(`at \\[${start},${start + 1}\\)`));
  }
  process.stdout.write("forged disjunction: an object read claimed at one arm where another object's test holds refused\n");
});
control(async (): Promise<void> => {
  // A spread of an intersection: Lean checks the copy against the clauses
  // it normalizes the operand's claim to, not against the producer's
  // reading. The copy of `{ k: string; t: number } & { k: "a" }` claimed at
  // `{ k: "b"; t: number }`, within the function's result, is refused at the
  // merge, in search and in checking.
  const good = run("spread-intersection-meet");
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "widened"), "widened function");
  const other = must(claims.functions.find(f => f.name === "other"), "other function");
  const start = source.indexOf("{ ...x }", source.indexOf("function widened"));
  const copy = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + "{ ...x }".length),
    "copy claim");
  copy.type = other.result;
  const forged = writeClaims(good, "spread-meet-forged", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "spread-meet-forged-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.match(result.stdout + result.stderr, new RegExp(`\\[${start},${start + "{ ...x }".length}\\)`));
  }
  process.stdout.write("spread of an intersection: a copy claimed at a field no operand's field gives refused at the merge, in search and in checking\n");
});
control(async (): Promise<void> => {
  // An array literal's spread is copied before a later element that runs
  // code, as JavaScript reads it there; a spread operand claimed at other
  // than an array is refused where the elements are produced and checked.
  const good = run("array-literal-spread");
  assert.equal(runExample("array-literal-spread", "snapshot()"), 22);
  const source = readFileSync(sourceKey(good), "utf8");
  const claims = readClaims(good);
  const fn = must(claims.functions.find(f => f.name === "appended"), "appended function");
  const start = source.indexOf("[...xs, x]") + "[...".length;
  const operand = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === start + 2), "spread operand claim");
  const number = claims.types.findIndex(r => Array.isArray(r) && r.length === 1 && r[0] === "num");
  assert(number >= 0);
  operand.type = [number];
  const forged = writeClaims(good, "array-spread-number", claims);
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "array-spread-forged-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
  }
});
control(async (): Promise<void> => {
  const good = run("constructor-tuple-spread");
  assert.equal(runExample("constructor-tuple-spread", "snapshot()"), 12);
  const source = readFileSync(sourceKey(good), "utf8");
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
    const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
      sourceKey(good), join(good, mode === "--produce-source-claims"
        ? "constructor-forged-evidence.json" : "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])]));
    assert.ifError(result.error);
    assert.equal(result.status, 1, result.stdout + result.stderr);
    assert.match(result.stdout + result.stderr, /constructor spread needs a tuple contract/);
  }
});
control(async (): Promise<void> => {
  const good = run("generic-prototype-instanceof");
  const ast: Ast = readFragmentFile(join(good, "fragment.json"));
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
      const result = tested(verifierCall(verifier, [mode, join(good, "fragment.json"), forged,
        sourceKey(good), join(good, mode === "--produce-source-claims"
          ? `prototype-${variant}-evidence.json` : "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : [])]));
      assert.ifError(result.error);
      assert.equal(result.status, 1, result.stdout + result.stderr);
      assert.match(result.stdout + result.stderr, variant === "unbound"
        ? /a label names a binder no unit or closure reads/
        : /evidence search failed|source evidence does not justify|source evidence refusal at/);
    }
  }
  process.stdout.write("prototype contracts: invented read types and unbound parameters refused in both modes\n");
});
control(async (): Promise<void> => {
  // A class's generic method, a closure the prototype holds, covers the
  // instance type's member up to renaming the member's binders to the
  // closure's: the renamed signatures must still follow from the closure's.
  // The class's declaration tampered to promise a number where the closure
  // returns its binder is refused at the construct code's return, where the
  // fresh instance meets the instance type; the untampered one is derived there.
  // `make` alone is kept, so the construct code is the first obligation.
  const classGeneric = run("class-generic-method");
  const source = readFileSync(sourceKey(classGeneric), "utf8");
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
});

control(async (): Promise<void> => {
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
    /source evidence (does not justify|refusal at)/);
  process.stdout.write("forged import closure: refused\n");
});
control(async (): Promise<void> => {
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
    writeFileSync(forged, must(JSON.stringify({ ...claims, types: [...claims.types, ...row] },
      (_key, value: unknown) => value === param.type ? type : value), "the forged claims' text"));
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
});

control(async (): Promise<void> => {
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
});
control(async (): Promise<void> => {
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
});
// A method or constructor claim is compared with its annotation by meaning, so
// another row for Values<number> is admitted; a domain wider than the
// annotation, here one that also admits undefined, is still refused.
control(async (): Promise<void> => {
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
});
control(async (): Promise<void> => {
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
});
control(async (): Promise<void> => {
  // The unannotated closure's body returns a number. Its claimed null result
  // is checked by the body's return obligation.
  const localClosure = run("closure-result-contract");
  const claims = readClaims(localClosure);
  const source = readFileSync(sourceKey(localClosure), "utf8");
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
});


control(async (): Promise<void> => {
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
});

control(async (): Promise<void> => {
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
});

control(async (): Promise<void> => {
  // The protocol's `next` bound to a union of hosts returns the union of
  // the hosts' results. A claim of one host's result alone, `Countdown`'s,
  // whose done value is `undefined`, is refused for the union whose other
  // host returns a string, as search and as evidence.
  const artifacts = run("bind-union-host");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  type Claim = SourceClaims["functions"][number]["expressions"][number];
  const boundNext = (name: string): Claim => {
    const s = source.indexOf("for (", source.indexOf(`export function ${name}(`));
    const q = source.indexOf(")", s);
    const fn = must(claims.functions.find((f) => f.name === name), name);
    return must(fn.expressions.find((e) => e.pos[0] === s && e.pos[1] === q + 1), `${name}'s bound next`);
  };
  const union = boundNext("total");
  union.type = structuredClone(boundNext("countdown").type);
  const forged = writeClaims(artifacts, "forged-union-host-next", claims);
  const searched = produceWith(artifacts, forged, "forged-union-host-next");
  const detail = searched.stdout + searched.stderr;
  assert.equal(searched.status, 1, detail);
  // Refused where the member is read and bound, the run from the header's
  // `(` to its `)`.
  const read = source.indexOf("(", union.pos[0]);
  assert.ok(detail.includes(`source expression obligation at [${read},${union.pos[1]})`), detail);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /claim|evidence/);
  process.stdout.write("bound next of a union of hosts: one host's result claimed alone refused\n");
});


control(async (): Promise<void> => {
  // Source arrows carry ordinary effects. Inject unequal member effects
  // into the fragment to exercise the producer's signature comparison.
  const artifacts = run("bind-union-host");
  const ast = readFragmentFile(join(artifacts, "fragment.json"));
  const host = must(ast.declarations.definitions.find(d => d.declaration.name === "Countdown"), "Countdown");
  assert.ok(host.expression?.k === "object");
  const next = must(host.expression.fields.find(f => f.name === "next"), "Countdown.next");
  assert.ok(next.type.k === "function");
  assert.deepEqual(next.type.effect, ordinaryEffect);
  next.type.effect = emptyEffect;
  const fragment = join(artifacts, "unequal-bound-member-effects.json");
  writeFileSync(fragment, JSON.stringify(ast));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", fragment]));
  assert.equal(lowered.status, 0, lowered.stdout + lowered.stderr);
  const flow = join(artifacts, "unequal-bound-member-effects-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposal = tested(producerCall(producerExecutable, [fragment, flow]));
  assert.equal(proposal.status, 2, proposal.stdout + proposal.stderr);
  assert.match(proposal.stdout + proposal.stderr,
    /a method bound to a union of hosts needs each host's member at one signature: the same parameters and effect/);
  process.stdout.write("unequal bound member effects: refused by the producer's union signature comparison\n");
});

for (const [file, name] of [["for-of-iterable-parameter", "first"], ["bind-union-host", "total"]]) control(async (): Promise<void> => {
  // Only the bound function's claimed effect changes. Its hosts' members
  // permit writes, so a claim preserving all locations needs refusal.
  const artifacts = run(file);
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const start = source.indexOf("for (", source.indexOf(`export function ${name}(`));
  const end = source.indexOf(")", start) + 1;
  const fn = must(claims.functions.find(f => f.name === name), name);
  const bound = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === end), `${name}'s bound next`);
  assert.ok(Array.isArray(bound.type) && bound.type.length === 1);
  const label = bound.type[0];
  assert.ok(typeof label === "number");
  const row = structuredClone(must(claims.types[label], "the bound function's row"));
  const arrows = row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []);
  assert.equal(arrows.length, 1);
  const arrow = must(arrows[0], "the bound signature");
  assert.deepEqual(arrow.effect, ordinaryEffect);
  arrow.effect = emptyEffect;
  const preserving = claims.types.push(row) - 1;
  // Mention both rows in the honest union so evidence and the forged claim
  // use the same graph labels. The ordinary arm admits the actual effect.
  bound.type.push(preserving);
  const honest = writeClaims(artifacts, `bound-${name}-effect-baseline`, claims);
  const baseline = produceWith(artifacts, honest, `bound-${name}-effect-baseline`);
  assert.equal(baseline.status, 0, baseline.stdout + baseline.stderr);
  bound.type = [preserving];
  const forged = writeClaims(artifacts, `forged-bound-${name}-effect`, claims);
  const searched = produceWith(artifacts, forged, `forged-bound-${name}-effect`);
  const detail = searched.stdout + searched.stderr;
  assert.equal(searched.status, 1, detail);
  const read = source.indexOf("(", start);
  assert.ok(detail.includes(`source expression obligation at [${read},${end})`), detail);
  const checked = invoke(forged, join(artifacts, `bound-${name}-effect-baseline-evidence.json`), artifacts);
  assert.ok(checked.includes(`source evidence refusal at [${read},${end})`), checked);
  process.stdout.write(`bound next effect of ${name}: excess preservation refused in search and checking at the binding\n`);
});

for (const name of ["countdown", "total"]) control(async (): Promise<void> => {
  // Dropping a receiver-store effect widens its restricted footprint:
  // the bound receiver can be any location in the caller's heap.
  const artifacts = run("bind-union-host");
  const ast = readFragmentFile(join(artifacts, "fragment.json"));
  for (const hostName of ["Countdown", "Repeat"]) {
    const host = must(ast.declarations.definitions.find(d => d.declaration.name === hostName), hostName);
    assert.ok(host.expression?.k === "object");
    const next = must(host.expression.fields.find(f => f.name === "next"), `${hostName}.next`);
    assert.ok(next.type.k === "function");
    next.type.effect = { ...emptyEffect, receiverStore: true };
  }
  // Keep this control at the binding. Class construction and other
  // functions retain annotations for the source's ordinary member effects.
  ast.functions = ast.functions.filter(f => f.name === name);
  ast.init = [];
  const fragment = join(artifacts, `receiver-store-${name}.json`);
  writeFileSync(fragment, JSON.stringify(ast));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", fragment]));
  assert.equal(lowered.status, 0, lowered.stdout + lowered.stderr);
  const flow = join(artifacts, `receiver-store-${name}-flow.json`);
  writeFileSync(flow, lowered.stdout);
  const proposal = tested(producerCall(producerExecutable, [fragment, flow]));
  assert.equal(proposal.status, 0, proposal.stdout + proposal.stderr);
  const proposed = join(artifacts, `receiver-store-${name}-claims.json`);
  writeFileSync(proposed, proposal.stdout);
  const claims = readClaimsFile(proposed);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const start = source.indexOf("for (", source.indexOf(`export function ${name}(`));
  const end = source.indexOf(")", start) + 1;
  const fn = must(claims.functions.find(f => f.name === name), name);
  const bound = must(fn.expressions.find(e => e.pos[0] === start && e.pos[1] === end), `${name}'s bound next`);
  assert.ok(Array.isArray(bound.type) && bound.type.length === 1);
  const label = bound.type[0];
  assert.ok(typeof label === "number");
  const row = structuredClone(must(claims.types[label], "the bound function's row"));
  const arrows = row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []);
  assert.equal(arrows.length, 1);
  const arrow = must(arrows[0], "the bound signature");
  assert.deepEqual(arrow.effect, ordinaryEffect);
  // The member read is separately claimed as a callable. Widen that
  // intermediate claim so this control tests the bound function's effect.
  const readStart = source.indexOf("(", start);
  const member = must(fn.expressions.find(e => e.pos[0] === readStart && e.pos[1] === end), "the member read");
  assert.ok(Array.isArray(member.type));
  for (const label of member.type) {
    assert.ok(typeof label === "number");
    for (const clause of must(claims.types[label], "the member callable's row")) {
      if (typeof clause === "object" && "arrs" in clause)
        for (const arrow of clause.arrs.arrows) arrow.effect = ordinaryEffect;
    }
  }
  arrow.effect = emptyEffect;
  const preserving = claims.types.push(row) - 1;
  // Mention both rows in the honest union so evidence and the forged claim
  // use the same graph labels. The ordinary arm admits the actual effect.
  bound.type.push(preserving);
  const honest = writeClaims(artifacts, `receiver-store-${name}-effect-baseline`, claims);
  const baseline = produceWith(artifacts, honest, `receiver-store-${name}-effect-baseline`, fragment);
  assert.equal(baseline.status, 0, baseline.stdout + baseline.stderr);
  bound.type = [preserving];
  const forged = writeClaims(artifacts, `forged-receiver-store-${name}-effect`, claims);
  const searched = produceWith(artifacts, forged, `forged-receiver-store-${name}-effect`, fragment);
  const detail = searched.stdout + searched.stderr;
  assert.equal(searched.status, 1, detail);
  const read = source.indexOf("(", start);
  assert.ok(detail.includes(`source expression obligation at [${read},${end})`), detail);
  const checked = invoke(forged, join(artifacts, `receiver-store-${name}-effect-baseline-evidence.json`), artifacts, fragment);
  assert.ok(checked.includes(`source evidence refusal at [${read},${end})`), checked);
  process.stdout.write(`bound receiver-store effect of ${name}: excess preservation refused in search and checking at the binding\n`);
});


control(async (): Promise<void> => {
  // A deferred closure body owns execution points separate from creation.
  const artifacts = run("closure-graph-try");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const fn = must(claims.functions[0], "guarded");
  const creation = must(fn.expressions.find((e) => e.pos[0] === source.indexOf("(): number =>")), "closure creation");
  const at = source.indexOf("return g();") + "return ".length;
  must(fn.expressions.find((e) => e.pos[0] === at && e.pos[1] === at + 3), "deferred call").point = creation.point;
  const forged = writeClaims(artifacts, "deferred-at-creation", claims);
  const deferred = produceWith(artifacts, forged, "deferred-at-creation");
  assert.notEqual(deferred.status, 0);
  assert.match(deferred.stdout + deferred.stderr, /expression claim at .*outside its execution point/);
  assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts), /expression claim at .*outside its execution point/);
});
control(async (): Promise<void> => {
  // A copied finalizer's source site belongs to each actual finalizer action.
  const artifacts = run("try-finally-jump");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A condition of a Boolean literal type takes one arm (`ifKnown`): claimed at
  // that arm alone, `ready || zs[0]` is `true`, as Node computes. The same claim
  // is refused at that expression where the condition is a binding a closure
  // resets before the arm is chosen, and Node finds `undefined` there.
  for (const [file, call, expected] of [
    ["known-condition", "known([])", true],
    ["invalid-known-condition", "stale([])", undefined],
  ] as const) {
    const artifacts = run(file);
    const source = readFileSync(sourceKey(artifacts), "utf8");
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
});
control(async (): Promise<void> => {
  // On `cell-union-capture`, whose captured cell is of a union of a
  // `null | boolean` arm and a `null` arm, a contents observation every arm
  // implies holds where the closure reads the cell, and a null-only one is
  // refused there, as one arm admits later Boolean writes. A statement entry's
  // null-only observation holds after the closure writes `null` into the cell,
  // and not where nothing wrote it; an entry narrowing the cell to its null arm
  // is refused at its entry, though its observation holds.
  const cellUnion = run("cell-union-capture");
  const source = readFileSync(sourceKey(cellUnion), "utf8");
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
      p.current = [[["value"], pick(l)]];
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
});
control(async (): Promise<void> => {
  // The result of a call through a captured union of functions is not narrowed
  // to one alternative's: claimed `true`, the call is refused where it is.
  const callableUnion = run("callable-union-capture");
  const source = readFileSync(sourceKey(callableUnion), "utf8");
  const claims = readClaims(callableUnion);
  const at = source.indexOf("f(unit)");
  must(claims.functions.flatMap((f) => f.expressions).find((e) => e.pos[0] === at && e.pos[1] === at + 7),
    "the call's claim").type = [rowOf(claims, { boolLit: { value: true } })];
  refusedAt(callableUnion, writeClaims(callableUnion, "forged-one-arm", claims), "forged-one-arm",
    `source expression obligation at [${at},${at + 7})`);
});
control(async (): Promise<void> => {
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
  const member = readFileSync(sourceKey(collections), "utf8").indexOf("cs.input1.merge");
  refusedAt(collections, writeClaims(collections, "forged-wider-rest", claims), "forged-wider-rest",
    `source expression obligation at [${member},${member + "cs.input1.merge".length})`);
});
control(async (): Promise<void> => {
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
    writeFileSync(forgedAst, must(JSON.stringify(ast), "the forged fragment's text"));
    return forgedAst;
  };
  for (const [artifacts, kind] of [[run("closure-result-contract"), "invoke"], [run("explicit-type-arguments"), "apply"]] as const)
    assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts,
      forgeTypeArgument(artifacts, kind)),
      /the call's instance is not the one its explicit type arguments state/);
});
control(async (): Promise<void> => {
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
    const source = readFileSync(sourceKey(artifacts), "utf8");
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
});
control(async (): Promise<void> => {
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
      /source evidence (does not justify the extracted program and exact claims|refusal at \[\d+,\d+\))/);
  }
});
control(async (): Promise<void> => {
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
    /does not justify|evidence refusal at|evidence search failed/);
});
control(async (): Promise<void> => {
  // A module function is reached at its own annotated signature, which Lean
  // reads from the source; a producer cannot retype the callee.
  const moduleFunctions = run("module-functions");
  const claims = readClaims(moduleFunctions);
  const source = readFileSync(sourceKey(moduleFunctions), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "twice"), "twice");
  const callee = source.indexOf("id(id(x))");
  const site = must(fn.expressions.find((e) => e.pos[0] === callee && e.pos[1] === callee + 2), "the outer callee's claim");
  site.type = must(fn.expressions.find((e) => e.pos[0] === source.indexOf("x))", callee)), "the argument's claim").type;
  invoke(writeClaims(moduleFunctions, "forged-callee", claims), join(moduleFunctions, "evidence.json"), moduleFunctions);
});
control(async (): Promise<void> => {
  // Only a module function without a rest parameter has its signature
  // extended by a rest of `unknown` in its slot: claiming one with a rest at
  // the longer signature its use expects is refused where it is read.
  const collects = run("invalid-named-function-arity");
  const claims = readClaims(collects);
  const source = readFileSync(sourceKey(collects), "utf8");
  const fn = must(claims.functions.find((f) => f.name === "widen"), "widen");
  const at = source.indexOf("collects;");
  must(fn.expressions.find((e) => e.pos[0] === at && e.pos[1] === at + "collects".length), "the read's claim").type = fn.result;
  refusedAt(collects, writeClaims(collects, "forged-collects-longer", claims), "forged-collects-longer",
    `source expression obligation at [${at},${at + "collects".length})`);
});
control(async (): Promise<void> => {
  // The initialization unit's claims are checked like a function's: claiming
  // the constant's initializer at another type is refused.
  const moduleInit = run("module-init");
  const claims = readClaims(moduleInit);
  const source = readFileSync(sourceKey(moduleInit), "utf8");
  const init = must(claims.init, "the initialization unit's claims");
  must(init.expressions.find((e) => e.pos[0] === source.indexOf("true;")), "the initializer's claim").type = [0];
  invoke(writeClaims(moduleInit, "forged-initializer", claims), join(moduleInit, "evidence.json"), moduleInit);
});
control(async (): Promise<void> => {
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
    const source = readFileSync(sourceKey(twoCalls), "utf8");
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
});
control(async (): Promise<void> => {
  // A graph certificate for the checked Boolean instance cannot validate a
  // different quantified contract. The scheme itself is independently consumed.
  const genericClosure = run("generic-closure");
  const claims = readClaims(genericClosure);
  const schemePoint = must(claims.functions[0], "the closure's function").expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type);
  assert.ok(schemePoint && !Array.isArray(schemePoint.type) && "scheme" in schemePoint.type);
  schemePoint.type.scheme.result = [1, 2];
  invoke(writeClaims(genericClosure, "forged-scheme", claims), join(genericClosure, "evidence.json"), genericClosure);
});
control(async (): Promise<void> => {
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
  const body = readFileSync(sourceKey(returned), "utf8").indexOf("value;");
  refusedAt(returned, writeClaims(returned, "forged-nested-claim", grounded), "forged-nested",
    `source expression obligation at [${body},${body + "value".length}): evidence search failed: no derivation of its return-contract claim`);
  const escaped = structuredClone(returnedClaims);
  const outside = must(must(escaped.functions[0], "the containing function").expressions.find(
    (e) => e.pos[0] > outer.pos[1] && Array.isArray(e.type)), "an expression after the closure");
  outside.type = nested.type;
  assert.match(invoke(writeClaims(returned, "forged-escape", escaped), join(returned, "evidence.json"), returned),
    /is not in scope/);
});
control(async (): Promise<void> => {
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
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});
control(async (): Promise<void> => {
  const artifacts = run("optional-read-observations");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find((f) => f.name === "observeOnly"), "optional observation function");
  const undef = rowOf(claims, "undef");
  const entry = must(fn.entries.find((e) => e.bindings.some((b) =>
    b.name === "obj" && b.current?.some(([[key], type]) => key === "val" &&
      type.length === 1 && type[0] === undef))), "undefined branch entry");
  const object = must(entry.bindings.find((b) => b.name === "obj"), "observed object");
  // The undefined branch cannot establish a number-valued read observation.
  object.current = [[["val"], [rowOf(claims, "num")]]];
  const forged = writeClaims(artifacts, "forged-optional-read-result", claims);
  refusedAt(artifacts, forged, "forged-optional-read-result", "source incoming edge obligation");
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
  assert.equal(runExample("invalid-optional-read-alias", "stale({ val: undefined })"), 1);
  assert.equal(runExample("invalid-optional-read-call",
    "(() => { const obj = { val: undefined }; return stale(obj, () => { obj.val = 1; }); })()"), 1);
});
control(async (): Promise<void> => {
  // A void parameter admits numbers and objects as well as undefined.
  // A forged singleton claim must fail at the parameter read.
  const artifacts = run("void-source-values");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "compareArguments"), "compareArguments's claims");
  const at = source.indexOf("left !== right");
  must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + 4),
    "the void argument read").type = [rowOf(claims, "undef")];
  const forged = writeClaims(artifacts, "forged-void-undefined", claims);
  refusedAt(artifacts, forged, "forged-void-undefined",
    `source expression obligation at [${at},${at + 4})`);
  invoke(forged, join(artifacts, "evidence.json"), artifacts);
});
control(async (): Promise<void> => {
  // An unconstrained source generic admits unknown, but its independently
  // extracted bound excludes calculus top and its internal stores.
  const artifacts = run("generic-unknown-arguments");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});
control(async (): Promise<void> => {
  checkGenericRest(verifier, run("generic-rest"));
  checkRestPackInstance(verifier, run("rest-pack-declared"), "emptyInfer()");
  checkRestPackInstance(verifier, run("class-rest-binder"), "new RestRunner(\n");
  checkOverloads(verifier, run("overloads"));
  checkDefaults(verifier, run("default-parameter-scope"));
  checkPatternDefaults(verifier, run("destructuring-known-default"));
  checkEarlyDefault(verifier, run("invalid-default-invocation"));
  checkSchemeDefaults(verifier, run("generic-default"));
  process.stdout.write("forged claims at each kind of point: read and checked there\n");
});

control(async (): Promise<void> => {
  // An array owns no `toJSON`, whatever the parser and the producer say: a
  // forged parameter type giving `nested`'s array one is refused by the
  // search and by the check of the evidence the original program earned.
  const artifacts = run("json-stringify-arrays");
  const ast = readFragmentFile(join(artifacts, "fragment.json"));
  const nested = must(ast.functions.find(f => f.name === "nested"), "nested's declaration");
  const rows = must(nested.params[0], "nested's parameter");
  const span = rows.type.span;
  rows.type = { k: "intersection", span, parts: [rows.type, { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "toJSON", optional: false, readonly: false, span, type: { k: "function", effect: ordinaryEffect,
      receiver: null, params: [], rest: null, result: { k: "atom", name: "undefined", span }, span } }] }] };
  const forged = join(artifacts, "forged-array-tojson.json");
  writeFileSync(forged, must(JSON.stringify(ast), "the forged fragment's text"));
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-array-tojson", forged);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /intersection is empty/);
  assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, forged),
    /intersection is empty/);
  process.stdout.write("an array owning toJSON, forged past the parser and the producer: refused by search and check\n");
});

control(async (): Promise<void> => {
  // An array acquires no `toJSON` by a write, whatever claims are offered.
  // The input is a valid array: claims and evidence are borrowed from a
  // weakened program whose declared `Hooked` and `View` are records with a
  // writable `toJSON`, then offered for the program itself, whose `Hooked` is
  // an array. The weakened declaration stays an intersection holding an
  // array, so both programs read the same declarations and the evidence
  // decodes against either. Search refuses at the write, directly and
  // through a structural view; consumption refuses the view's write where it
  // is, and the direct evidence, which the weakened program's check accepts,
  // for the program whose `Hooked` is an array.
  const borrow = (file: string): { artifacts: string; claims: string; evidence: string } => {
    const artifacts = run(file);
    const ast: Ast = readFragmentFile(join(artifacts, "fragment.json"));
    const weakened = ast.declarations.definitions.filter(d => ["Hooked", "View"].includes(d.declaration.name));
    assert.ok(weakened.some(d => d.declaration.name === "Hooked"), "the declared array type");
    const record = (name: string, type: TypeTerm): TypeTerm => ({ k: "object", span: [0, 0], stringIndex: null,
      calls: [], fields: [{ name, optional: false, readonly: false, span: [0, 0], type }] });
    for (const definition of weakened)
      definition.expression = { k: "intersection", span: [0, 0], parts: [
        record("toJSON", { k: "function", effect: ordinaryEffect, receiver: null, params: [], rest: null,
          result: { k: "atom", name: "undefined", span: [0, 0] }, span: [0, 0] }),
        record("items", { k: "array", presence: "readable", readonly: false, span: [0, 0],
          element: { k: "atom", name: "number", span: [0, 0] } })] };
    const weak = join(artifacts, "weakened-array-tojson.json");
    writeFileSync(weak, JSON.stringify(ast));
    const lowered = tested(verifierCall(verifier, ["--lower-control-flow", weak]));
    assert.equal(lowered.status, 0, lowered.stderr);
    const flow = join(artifacts, "weakened-array-tojson-flow.json");
    writeFileSync(flow, lowered.stdout);
    const proposed = tested(producerCall(producerExecutable, [weak, flow]));
    assert.equal(proposed.status, 0, proposed.stderr);
    const claims = join(artifacts, "weakened-array-tojson-claims.json");
    writeFileSync(claims, proposed.stdout);
    const borrowed = produceWith(artifacts, claims, "weakened-array-tojson", weak);
    assert.equal(borrowed.status, 0, borrowed.stdout + borrowed.stderr);
    const evidence = join(artifacts, "weakened-array-tojson-evidence.json");
    const accepted = tested(verifierCall(verifier, ["--check-source-claims", weak, claims, sourceKey(artifacts), evidence]));
    assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
    return { artifacts, claims, evidence };
  };
  const direct = borrow("invalid-array-tojson-write");
  const source = readFileSync(sourceKey(direct.artifacts), "utf8");
  const at = source.indexOf("xs.toJSON = f");
  const searched = produceWith(direct.artifacts, direct.claims, "forged-array-tojson-write");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const failure = readDiagnostic(searched.stdout + searched.stderr);
  assert.equal(failure?.kind, "node-typing");
  assert.deepEqual(failure?.source?.sourceMap?.pos, [at, at + "xs.toJSON = f".length]);
  const term = failure?.sequent?.term;
  assert.ok(term?.kind === "writeAt");
  assert.equal(term.field, "toJSON");
  // The evidence's equations read `Hooked` as the weakened record. The
  // weakened program differs from this one only there, and its check accepts
  // the same evidence, so the refusal is the array's: at the write, whose
  // node the evidence claims otherwise.
  assert.match(invoke(direct.claims, direct.evidence, direct.artifacts),
    new RegExp(`^reject: source evidence refusal at \\[${at},${at + "xs.toJSON = f;".length}\\)`, "m"));
  const view = borrow("invalid-array-tojson-view");
  const viewSource = readFileSync(sourceKey(view.artifacts), "utf8");
  const viewAt = viewSource.indexOf("alias.toJSON = f");
  const refusal = `source refusal at [${viewAt},${viewAt + "alias.toJSON = f".length}): a write of 'toJSON'`;
  const viewSearched = produceWith(view.artifacts, view.claims, "forged-array-tojson-view");
  assert.equal(viewSearched.status, 1, viewSearched.stdout + viewSearched.stderr);
  assert.ok((viewSearched.stdout + viewSearched.stderr).includes(refusal), viewSearched.stdout + viewSearched.stderr);
  assert.ok(invoke(view.claims, view.evidence, view.artifacts).includes(refusal));
  process.stdout.write("an array given toJSON by a write, on borrowed claims and evidence: refused at the write, " +
    "directly and through a view\n");
});

control(async (): Promise<void> => {
  // A signal listener is called with the signal's name, whatever claims are
  // offered: claims and evidence borrowed from a weakened document whose
  // `process.on` takes a listener of a number at the signals are accepted
  // there and refused for the reviewed one, in search at the call and in
  // checking.
  const artifacts = run("invalid-collections-process-listener");
  const ast: Ast = readFragmentFile(join(artifacts, "fragment.json"));
  const global = must(ast.declarations.definitions.find(d => d.declaration.name === "process"), "the process global");
  const expression = global.expression;
  assert.ok(expression?.k === "object");
  const on = must(expression.fields.find(f => f.name === "on"), "process.on");
  const weaken = (t: TypeTerm): TypeTerm => t.k === "intersection" ? { ...t, parts: t.parts.map(weaken) }
    : t.k === "function" ? { ...t, params: t.params.map((p, i): TypeTerm => i === 1 && p.k === "function"
      ? { ...p, params: [{ k: "atom", name: "number", span: p.span }] } : p) }
    : t;
  on.type = weaken(on.type);
  const weak = join(artifacts, "weakened-process-on.json");
  writeFileSync(weak, JSON.stringify(ast));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", weak]));
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(artifacts, "weakened-process-on-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposed = tested(producerCall(producerExecutable, [weak, flow]));
  assert.equal(proposed.status, 0, proposed.stderr);
  const claims = join(artifacts, "weakened-process-on-claims.json");
  writeFileSync(claims, proposed.stdout);
  const borrowed = produceWith(artifacts, claims, "weakened-process-on", weak);
  assert.equal(borrowed.status, 0, borrowed.stdout + borrowed.stderr);
  const evidence = join(artifacts, "weakened-process-on-evidence.json");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const at = source.indexOf("process.on(\"SIGTERM\", listener)");
  const searched = produceWith(artifacts, claims, "forged-process-on");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const failure = readDiagnostic(searched.stdout + searched.stderr);
  assert.equal(failure?.kind, "node-typing");
  // The invoke is located at its callee, `process.on`.
  assert.deepEqual(failure?.source?.sourceMap?.pos, [at, at + "process.on".length]);
  invoke(claims, evidence, artifacts);
  process.stdout.write("a number listener at a signal, on borrowed claims and evidence: refused at the call and in checking\n");
});

control(async (): Promise<void> => {
  // Own-key exclusion preserves the inherited constructor read. A forged
  // undefined claim must fail both search and evidence consumption.
  const artifacts = run("native-promise-constructor-read");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
  const weakAst: Ast = readFragmentFile(join(write, "fragment.json"));
  const promise = must(weakAst.declarations.definitions.find(d =>
    d.declaration.name === "Promise" && d.declaration.module.startsWith("typescript/lib/")),
    "the native Promise declaration");
  assert(promise.expression?.k === "object" && promise.expression.prototype?.k === "object");
  promise.expression.prototype.fields = promise.expression.prototype.fields.filter(f => f.name !== "constructor");
  promise.expression.fields.push({ name: "constructor", optional: false, readonly: false,
    type: { k: "atom", name: "unknown", span: [0, 0] }, span: [0, 0] });
  const weak = join(write, "weakened-native-constructor.json");
  writeFileSync(weak, JSON.stringify(weakAst));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", weak]));
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(write, "weakened-native-flow.json");
  writeFileSync(flow, lowered.stdout);
  const proposed = tested(producerCall(producerExecutable, [weak, flow]));
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
});

control(async (): Promise<void> => {
  // Widening a generic wrapper's result preserves its input qualification.
  // Forging an unbounded target must fail search and accepted-evidence replay.
  const artifacts = run("native-promise-qualified-return");
  const ast: Ast = readFragmentFile(join(artifacts, "fragment.json"));
  const target = must(ast.declarations.definitions.find(d => d.declaration.name === "NumericUnknownWrapper"),
    "the result-widened generic wrapper declaration").expression;
  assert.ok(target?.k === "scheme" && target.binders.length === 1);
  must(target.binders[0], "the retained numeric input binder").bound = null;
  const forged = join(artifacts, "forged-generic-input-bound.json");
  writeFileSync(forged, JSON.stringify(ast));
  const claims = join(artifacts, "claims.json");
  const searched = produceWith(artifacts, claims, "forged-generic-input-bound", forged);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const at = source.indexOf("wrapper;", source.indexOf("function widenResult"));
  assert.ok((searched.stdout + searched.stderr).includes(
    `source expression obligation at [${at},${at + "wrapper".length})`), searched.stdout + searched.stderr);
  invoke(claims, join(artifacts, "evidence.json"), artifacts, forged);
});

control(async (): Promise<void> => {
  // Scheme matching must keep both the native receiver bound and finally's
  // fixed cleanup result contract. These forged methods broaden one operand.
  const artifacts = run("native-promise-reactions");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
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
});

// A footprint claim forged onto a callback is certified only where its body
// is within it: one reading its arguments is within the empty footprint; one
// writing a cell it captures, a `Map`'s internal slots through `set`, or a
// fresh `Set`'s through `add` is within `{value: any, store: keep}` and not
// the empty one; one calling a member stated unrestricted (`pop` on the source
// beside a string's `trim` or alone, `Object.entries` of an interface's
// object) or beyond the footprint (a global regex's
// `test`) is refused at its own typing, even at the footprint `map`'s dense
// signature accepts. One calling `forEachChild` is within its visitor's
// footprint: a visitor growing an array the callback allocated is within
// `{value: any, store: grow}`, and its callback within neither the empty
// footprint nor `{value: any, store: keep}`; a popping one within neither
// the empty footprint nor `grow`. One calling a sync API request is within
// `{value: any, store: grow}` and not `{value: any, store: keep}`. A refused control marked `consumed` also checks the
// fixture's honest evidence against the forged claim, which must refuse; its
// fixture verifies, so that evidence exists: program 7 at a result type
// admitting holes (`map-unstable-pop-sparse`) is consumed so. A negative
// fixture has no evidence, and its control is production only.
const keepAll: ClosedFootprint = { value: "keep", store: "keep" };
const writeValues: ClosedFootprint = { value: "any", store: "keep" };
const growStores: ClosedFootprint = { value: "any", store: "grow" };
control(async (): Promise<void> => {
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
    ["object-entries-sparse", "(n) =>", 3, false, keepAll, true],
    ["invalid-object-entries-preserving", "(n) =>", 3, false, keepAll, false],
    ["invalid-compiler-api-visitor-effect", "(n) => {", 3, false, keepAll, false],
    ["invalid-compiler-api-visitor-effect", "(n) => {", 3, false, growStores, false],
    ["compiler-api-visitor-effect", "(n) => {", 3, false, keepAll, true],
    ["compiler-api-visitor-effect", "(n) => {", 3, false, writeValues, true],
    ["compiler-api-request-effect", "(n) =>", 3, false, writeValues, true],
    ["compiler-api-request-effect", "(n) =>", 3, true, growStores, true],
    ["invalid-compiler-api-request-tojson", "() =>", 3, false, growStores, false],
    ["compiler-api-visitor-pop-sparse", "(n) => {", 3, false, keepAll, true],
    ["compiler-api-visitor-pop-sparse", "(n) => {", 3, false, growStores, true],
  ] as const) {
    const artifacts = run(file);
    const claims = readClaims(artifacts);
    const source = readFileSync(sourceKey(artifacts), "utf8");
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
      const consume = tested(verifierCall(verifier, ["--check-source-claims", join(artifacts, "fragment.json"),
        input, sourceKey(artifacts), join(artifacts, "qualified-callback-evidence.json")]));
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
      assert.equal(present(join(artifacts, "evidence.json")), consumed,
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
});

control(async (): Promise<void> => {
  // `split`'s non-empty form is selected by its separator's type: the
  // separator `"\n"` forged at `string` takes the general form, whose first
  // element may be undefined, so search refuses it, and checking the honest
  // evidence, which selected the non-empty form, refuses it there.
  const artifacts = run("split-non-empty");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // The non-empty form's store contract forbids a removal: a call whose
  // result is shrunk (popped, through an alias) or held at `string[]`, its
  // honest evidence at the general form, forged at `[string, ...string[]]`,
  // is refused in search and in checking, whatever the producer proposes.
  const artifacts = run("split-non-empty");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A receiver claimed without its `undefined` takes no nullish guard: the
  // read of `b` in `b.n`, a parameter that may be absent, forged at the box
  // alone, is refused in search, and checking the honest evidence, whose
  // guard the forged claim no longer lowers, refuses it there.
  const artifacts = run("nullish-member-reads");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A fresh result forged onto code returning its parameter, a constant whose
  // value a callback pops: the code's returns are checked to return a store
  // allocated by its run, and the parameter's is not, so search refuses the
  // claim and checking the honest evidence against it refuses it there.
  const artifacts = run("map-stable-fresh-store");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A footprint claim forged onto classes' construct signatures is checked
  // against their constructors' code: a constructor writing a module cell is
  // refused within the empty footprint, at its own typing, located in its
  // class, while one adding keys to its instance, an allocation, is within
  // it; the honest evidence checked against the forged claim is a footprint
  // refusal located there too.
  const artifacts = run("class-constructor-effect");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const classes: [number, number] = [source.indexOf("class Counted"), source.indexOf("class Plain")];
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
  process.stdout.write("construct footprint claim {keep, keep}, class-constructor-effect: refused at the cell write\n");
});

control(async (): Promise<void> => {
  // A construction forged to the other stated form's result: `new Set` of a
  // string claimed at the `Set<number>` the array construction has. The
  // construction rule requires the selected signature with every argument's
  // premise, so search refuses it, and so does checking the honest evidence
  // against the forged claim.
  const artifacts = run("set-string-construction");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // An optional call's body is claimed at no value only where its receiver
  // is only nullish. The loop's receiver holds the array from the second
  // iteration on: the body's member read and call forged to no value are
  // refused, whatever the producer proposes.
  const artifacts = run("optional-call-loop-cell");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A module constant's arrow is claimed at its signature extended by a rest
  // of `unknown`, which Lean checks against the arrow itself: the extension
  // forged to take `unknown` at the arrow's `string` parameter is refused
  // where the arrow is created.
  const artifacts = run("arrow-constant-callback");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // `%Dispatch:replace%` states heap preservation only at a target whose
  // `[Symbol.replace]` states it. A global regex's does not: an instance of
  // the dispatch claimed preserving at that target, with the callback
  // claimed preserving through it, is refused at the callback's typing,
  // whatever the producer proposes, and checking the honest evidence against
  // the forged claims is a footprint refusal.
  const artifacts = run("map-stable-regexp-replace");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
  assert.ok(present(join(artifacts, "evidence.json")), "the fixture's honest evidence");
  assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts),
    /source effect refusal at \[\d+,\d+\): the footprint claimed for/);
  process.stdout.write("forged dispatch effect: a global regex's replacement refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A declaration's claimed footprint is established by its own unit's
  // graph. `collect` steps an array iterator, which writes its position,
  // and pushes onto its parameter: it is within `{value: any, store: grow}`
  // and verifies there. Claimed at a footprint not covering that one,
  // evidence production refuses at a node of its body, and the evidence for
  // the honest claims does not justify the forged ones.
  const artifacts = run("optional-call-loop-cell");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A footprint on a throw is established by the unit's own graph, and a
  // handler is certified only around a call whose signature states it.
  // `largest` calls `Math.max`, which states its footprint on normal return
  // only: claimed on a throw, it is refused at its call. `checked` states it;
  // claimed without, `orZero`'s callback, which reads `checked` at the
  // signature stating it, is refused.
  // Each in evidence production and in checking.
  const artifacts = run("exceptional-footprint-handler");
  const honest = readClaims(artifacts);
  assert.equal(must(honest.functions.find(f => f.name === "checked"), "checked's claims").onThrow, true);
  assert.equal(must(honest.functions.find(f => f.name === "largest"), "largest's claims").onThrow, false);
  for (const [name, forge, at] of [
    ["forged-throw-footprint-largest", (c: SourceClaims) => {
      must(c.functions.find(f => f.name === "largest"), "largest's claims").onThrow = true;
    }, /source effect refusal at \[\d+,\d+\): the footprint claimed for 'largest'/],
    ["forged-throw-footprint-checked", (c: SourceClaims) => {
      must(c.functions.find(f => f.name === "checked"), "checked's claims").onThrow = false;
    }, /reject: source (expression obligation at \[\d+,\d+\)|evidence does not justify|evidence refusal at)/],
  ] as const) {
    const claims = readClaims(artifacts);
    forge(claims);
    const input = writeClaims(artifacts, name, claims);
    const produce = produceWith(artifacts, input, name);
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, produce.stdout + produce.stderr);
    for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)])
      assert.match(detail, at);
  }
  process.stdout.write("forged throw footprints: a caller of Math.max claimed on a throw, and a handler around a call claimed without, refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A node never returns normally only where its checked typing is empty
  // (`no-return`). `stop(xs)` returns a `Promise<never>`, a value: claimed at
  // `never`, with the callback calling it claimed within the empty
  // footprint, search refuses the call's typing.
  const artifacts = run("invalid-no-return-promise");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const at = source.indexOf("stop(xs);");
  const expressions = claims.functions.flatMap(f => f.expressions);
  must(expressions.find(e => e.pos[0] === at && e.pos[1] === at + "stop(xs)".length), "the call's claim").type = [];
  const closure = must(expressions.find(e => e.pos[0] === source.indexOf("(x) => {")), "the callback's claim");
  assert.ok(Array.isArray(closure.type) && closure.type.length === 1 && typeof closure.type[0] === "number");
  const arrow = must(must(claims.types[closure.type[0]], "the callback's type row").flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []).find(s => s.arguments.length === 3),
    "the callback contract");
  arrow.effect = footprintEffect(keepAll);
  const input = writeClaims(artifacts, "forged-no-return-promise", claims);
  const produce = produceWith(artifacts, input, "forged-no-return-promise");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const failure = readDiagnostic(produce.stdout + produce.stderr);
  assert.ok(failure && failure.kind === "node-typing", produce.stdout + produce.stderr);
  assert.deepEqual(failure.source?.sourceMap?.pos, [at, at + "stop(xs)".length], "refused at the call's typing");
  process.stdout.write("forged no-return node: a call returning Promise<never> claimed at never refused in search at its typing\n");
});

mutationControl(async (): Promise<void> => {
  // A no-return node at a type a value meets: `gate.fail("empty")` returns
  // `never`, so its claim at `string` is a valid typing, under which the
  // call may return. The callback's claim within `{keep, keep}` is refused
  // in search; with the emptiness decision removed (the `empty` mutation)
  // search certifies it, and checking that evidence refuses it, so the
  // emptiness decision alone refuses it.
  const artifacts = run("no-return-callee-map");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const at = source.indexOf('gate.fail("empty")');
  const call = must(must(claims.functions.find(f => f.name === "members"), "members' claims").expressions
    .find(e => e.pos[0] === at && e.pos[1] === at + 'gate.fail("empty")'.length), "the call's claim");
  assert.deepEqual(call.type, [], "the call is claimed at never");
  call.type = [rowOf(claims, "str")];
  const name = "forged-no-return-nonempty";
  const input = writeClaims(artifacts, name, claims);
  const produce = produceWith(artifacts, input, name);
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  invoke(input, forgedEvidence(artifacts, input, name, "empty"), artifacts);
  process.stdout.write("forged no-return node at a non-empty type: gate.fail typed string in a callback claimed at {keep, keep} refused in search and in checking, certified only without the emptiness decision\n");
});

mutationControl(async (): Promise<void> => {
  // An async definition's effect is certified at `top` (`asyncEffects`): an
  // async call returns its promise where its body throws. `rejected`, and
  // the async arrow `rejecting` returns, reach no completion: each calls a
  // never-returning `stop`, then throws, so on normal return each body is
  // within the empty footprint (`no-return`). Claimed at `{keep, keep}`,
  // search refuses at the definition; with that check removed (the `async`
  // mutation) search certifies the forged claims, and checking that
  // evidence refuses them at the definition, so the check alone refuses
  // them.
  const artifacts = run("no-return-callee-map");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const forgeries: [string, (c: SourceClaims) => void][] = [
    ["forged-async-declaration", (c) => {
      must(c.functions.find(f => f.name === "rejected"), "rejected's claims").footprint = keepAll;
    }],
    ["forged-async-closure", (c) => {
      const closure = must(c.functions.flatMap(f => f.expressions).find(e => e.pos[0] === source.search(/async \(\s*ys/)),
        "the async arrow's claim");
      assert.ok(Array.isArray(closure.type) && closure.type.length === 1 && typeof closure.type[0] === "number");
      // A row of its own: the function's result claim shares the honest one.
      const row = structuredClone(must(c.types[closure.type[0]], "the arrow's type row"));
      must(row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])
        .find(s => s.arguments.length === 2), "the arrow's contract").effect = footprintEffect(keepAll);
      closure.type = [c.types.push(row) - 1];
    }],
    // The async recursive constant `countdown`, whose closure reads its self
    // entry at the footprint its claim states.
    ["forged-async-recursive", (c) => {
      const closure = must((c.init?.expressions ?? []).find(e => e.pos[0] === source.search(/async \(\s*n:/)),
        "countdown's closure claim");
      assert.ok(Array.isArray(closure.type) && closure.type.length === 1 && typeof closure.type[0] === "number");
      // Its row in place: the binding, the self entry and the recursive
      // call read the same row, which no annotation fixes.
      for (const s of must(c.types[closure.type[0]], "countdown's type row").flatMap(clause =>
        typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])) s.effect = footprintEffect(keepAll);
    }],
  ];
  for (const [name, forge] of forgeries) {
    const claims = readClaims(artifacts);
    forge(claims);
    const input = writeClaims(artifacts, name, claims);
    const produce = produceWith(artifacts, input, name);
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, produce.stdout + produce.stderr);
    // Checked against the evidence search produces for the forged claims
    // without the check (a new effect type renumbers the store the honest
    // evidence refers to).
    const generated = forgedEvidence(artifacts, input, name, "async");
    for (const detail of [produce.stdout + produce.stderr, invoke(input, generated, artifacts)])
      assert.match(detail, /source effect refusal at \[\d+,\d+\): the footprint claimed for .* is not `top`, and an async definition's is/, name);
  }
  process.stdout.write("forged async footprints: an async function, an async arrow and an async recursive constant reaching no completion, claimed at {keep, keep}, refused in search and in checking, certified only without the async check\n");
});

mutationControl(async (): Promise<void> => {
  // A stated declaration's claim lies within its statement (L2,
  // `statedWithin`): `third`, stating the empty footprint, which no code
  // calls, claimed at `{value: any, store: grow}`, which its pure body
  // meets, is refused in search and in checking at the definition; with
  // that check removed (the `stated` mutation) search certifies the forged
  // claim.
  const artifacts = run("method-effect-declaration");
  const claims = readClaims(artifacts);
  must(claims.functions.find(f => f.name === "third"), "third's claims").footprint = { value: "any", store: "grow" };
  const name = "forged-stated-declaration";
  const input = writeClaims(artifacts, name, claims);
  const produce = produceWith(artifacts, input, name);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const generated = forgedEvidence(artifacts, input, name, "stated");
  for (const detail of [produce.stdout + produce.stderr, invoke(input, generated, artifacts)])
    assert.match(detail, /source effect refusal at \[\d+,\d+\): the footprint claimed for 'third' is not within the effect its result annotation states/);
  process.stdout.write("forged stated declaration: a claim above its statement refused in search and in checking, certified only without the stated check\n");
});

mutationControl(async (): Promise<void> => {
  // A stated closure's code covers its statement over its annotation's
  // whole domain (L2, `lambdaSetup`). `bad`, a stated arrow popping the
  // array it is handed, which no code calls, claimed at the footprint
  // letting everything change, which its code meets: refused in search and
  // in checking; with the requirement removed (the `stated` mutation)
  // search certifies it. `flagged`, popping where its flag is `true`,
  // claimed at a flag of `false` alone and the empty footprint, which its
  // code meets there: refused for offering no row over the whole domain.
  type ClaimArrow = Extract<SourceClaims["types"][number][number], { arrs: unknown }>["arrs"]["arrows"][number];
  const forge = (file: string, at: RegExp, name: string, change: (s: ClaimArrow) => void): {
    artifacts: string; input: string } => {
    const artifacts = run(file);
    const claims = readClaims(artifacts);
    const source = readFileSync(sourceKey(artifacts), "utf8");
    const closure = must((claims.init?.expressions ?? []).find(e => e.pos[0] === source.search(at)), `${file}'s closure claim`);
    assert.ok(Array.isArray(closure.type) && closure.type.length === 1 && typeof closure.type[0] === "number");
    const row = structuredClone(must(claims.types[closure.type[0]], `${file}'s type row`));
    for (const s of row.flatMap(clause => typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])) change(s);
    closure.type = [claims.types.push(row) - 1];
    return { artifacts, input: writeClaims(artifacts, name, claims) };
  };
  const refusal = /a stated closure's claim must offer its stated effect over its annotated parameters/;
  const weaker = forge("invalid-method-effect-unused", /\(\s*xs: number\[\],?\s*\)/, "forged-stated-weaker", s => { s.effect = ordinaryEffect; });
  const produce = produceWith(weaker.artifacts, weaker.input, "forged-stated-weaker");
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const generated = forgedEvidence(weaker.artifacts, weaker.input, "forged-stated-weaker", "stated");
  for (const detail of [produce.stdout + produce.stderr, invoke(weaker.input, generated, weaker.artifacts)])
    assert.match(detail, refusal);
  const tru = 1, fls = 2;
  const narrowed = forge("invalid-method-effect-narrowed", /\(\s*xs: number\[\],\s*flag/, "forged-stated-narrowed", s => {
    assert.deepEqual(s.arguments[1], [tru, fls], "the flag's claim is boolean");
    s.arguments[1] = [fls];
  });
  const searched = produceWith(narrowed.artifacts, narrowed.input, "forged-stated-narrowed");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, refusal);
  process.stdout.write("forged stated closures: a weaker effect refused in search and in checking, certified only without the full-domain requirement; a narrowed domain at a covering effect refused in search\n");
});

control(async (): Promise<void> => {
  // A generic closure states no effect: its rows bind its binders at the
  // bounds its claim states, which need not cover its own. The parser
  // refuses the statement; with one written into the Fragment of a verified
  // generic closure, Lean refuses it too, in search.
  const artifacts = run("generic-function-type-annotation");
  const fragment = readFileSync(join(artifacts, "fragment.json"), "utf8");
  const lambda = fragment.search(/"k":"lambda","pos":\[\d+,\d+\],"typeParams":\[\{/);
  assert.ok(lambda >= 0, "a generic closure");
  const unstated = fragment.indexOf('"stated":null', lambda);
  assert.ok(unstated > lambda, "its statement");
  const fragmentPath = join(artifacts, "forged-generic-stated-fragment.json");
  writeFileSync(fragmentPath, fragment.slice(0, unstated) +
    '"stated":{"footprint":{"value":"keep","store":"keep"},"onThrow":false}' + fragment.slice(unstated + '"stated":null'.length));
  const produce = produceWith(artifacts, join(artifacts, "claims.json"), "forged-generic-stated", fragmentPath);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  assert.match(produce.stdout + produce.stderr, /a generic closure states no effect/);
  process.stdout.write("stated generic closure: a statement written into the Fragment refused in search\n");
});

control(async (): Promise<void> => {
  // A class method's statement is part of the instance type's member, so
  // the class's construction is checked against it whatever the method's
  // own obligation (L3): with the Fragment's `stated` of `bump` dropped and
  // its closure claimed at the footprint letting everything change, which
  // its popping body meets, the class is still refused, at its
  // construction.
  const artifacts = run("invalid-method-effect-construction");
  const fragment = readFileSync(join(artifacts, "fragment.json"), "utf8");
  const statement = '"stated":{"footprint":{"value":"keep","store":"keep"},"onThrow":false}';
  assert.equal(fragment.split(statement).length, 2, "bump's statement");
  const fragmentPath = join(artifacts, "forged-unstated-fragment.json");
  writeFileSync(fragmentPath, fragment.replace(statement, '"stated":null'));
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const closure = must((claims.init?.expressions ?? []).find(e => e.pos[0] === source.indexOf("bump(")),
    "bump's closure claim");
  assert.ok(Array.isArray(closure.type) && closure.type.length === 1 && typeof closure.type[0] === "number");
  // Its row in place: the method's binding and the prototype's field read
  // the same row, which no annotation fixes.
  for (const s of must(claims.types[closure.type[0]], "bump's type row").flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : [])) s.effect = ordinaryEffect;
  const name = "forged-unstated-method";
  const input = writeClaims(artifacts, name, claims);
  const produce = produceWith(artifacts, input, name, fragmentPath);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  const at = source.indexOf("Bump {");
  assert.match(produce.stdout + produce.stderr,
    new RegExp(`source expression obligation at \\[${at},${at + "Bump".length}\\): evidence search failed: no derivation of its return-contract claim`));
  process.stdout.write("unstated method of a stated member: the class's construction refused in search, the Fragment's statement dropped\n");
});

control(async (): Promise<void> => {
  // A statement read across modules is the import assumption (SOURCE-ELABORATION.md,
  // "Stated effects"): the importer of `drain`, which pops while stating
  // the empty footprint, verifies relative to it, and `drain`'s own module's
  // run refuses the statement.
  run("stated-assumed-value-import");
  const project = resolve(here, "imports-project");
  const outcome = check(join(project, "stated.ts"), tsconfigOf(project));
  if (outcome.status === "verified") assert.fail("drain's module verified");
  assert.match(outcome.detail, /the footprint claimed for 'drain' is not established by its body/);
  process.stdout.write("stated import: the importer verified relative to the import assumption, the exporting module's run refused\n");
});

control(async (): Promise<void> => {
  // A field's observed contents exclude an arm only once every test it
  // failed rules the arm's field type out: after `kind` failed "a", the arm
  // `{ kind: "a" | "b" }` may still hold "b". Claimed excluded there, the
  // edge is refused where evidence is produced and where it is checked.
  const artifacts = run("field-contents-exclusion");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const chained = must(claims.functions.find(f => f.name === "chained"), "chained's claims");
  const at = source.indexOf(`if (k.kind === "b")`, source.indexOf("function chained"));
  const entry = must(chained.entries.find(e => e.start === at), "the entry of the test for b");
  const after = must(chained.entries.find(e => e.start === source.indexOf(`if (k.kind === "c")`, at)), "the entry of the test for c");
  const binding = must(entry.bindings.find(b => b.name === "k"), "k at the test for b");
  binding.type = must(after.bindings.find(b => b.name === "k"), "k at the test for c").type;
  const input = writeClaims(artifacts, "forged-field-contents-exclusion", claims);
  const produce = produceWith(artifacts, input, "forged-field-contents-exclusion");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)])
    assert.match(detail, /reject: source (incoming edge obligation|expression obligation|evidence does not justify|evidence refusal at)/);
  process.stdout.write("forged field contents: an arm excluded before its field failed every value refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A test's answer is a fact of the field, or of a dictionary's entry, only
  // where an edge establishes it. Claimed where the field is untested, or
  // past a write that may alias it or a call, the read at the test's slice is
  // refused where evidence is produced and where it is checked.
  for (const [file, afterNames] of [["field-tag-read", ["afterWrite", "afterCall"]],
      ["dictionary-field-tag-read", ["afterCall"]]] as const) {
    const artifacts = run(file);
    const source = readFileSync(sourceKey(artifacts), "utf8");
    const claims = readClaims(artifacts);
    const size = must(claims.functions.find(f => f.name === "size"), "size's claims");
    const tested = source.indexOf("return t.mapping.map", source.indexOf("function size"));
    const after = must(size.entries.find(e => e.start === tested), "the entry past the test");
    const first = must(size.entries.find(e => e.start === source.indexOf("if (!Array.isArray", source.indexOf("function size"))),
      "the entry of the test");
    must(first.bindings.find(b => b.name === "t"), "t at the test").current =
      must(after.bindings.find(b => b.name === "t"), "t past the test").current;
    const input = writeClaims(artifacts, "forged-field-tag-before", claims);
    const produce = produceWith(artifacts, input, "forged-field-tag-before");
    assert.ifError(produce.error);
    assert.equal(produce.status, 1, produce.stdout + produce.stderr);
    for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)])
      assert.match(detail, /reject: source (incoming edge obligation|expression obligation|evidence does not justify|evidence refusal at)/);
    // Past the aliasing write and past the call, the honest claims read the
    // field at its type; claims keeping the test's fact there are refused.
    for (const name of afterNames) {
      const claims = readClaims(artifacts);
      const fn = must(claims.functions.find(f => f.name === name), `${name}'s claims`);
      const from = source.indexOf(`function ${name}`);
      const test = source.indexOf("Array.isArray", from);
      const ret = source.indexOf("return t.mapping;", from);
      const between = must(fn.entries.filter(e => e.start > test && e.start < ret)
        .find(e => e.bindings.some(b => b.name === "t" && b.current !== null)), `${name}: the entry holding the test's fact`);
      const fact = must(between.bindings.find(b => b.name === "t")?.current, `${name}: the test's fact`);
      const at = must(fn.entries.find(e => e.start === ret), `${name}: the read's entry`);
      must(at.bindings.find(b => b.name === "t"), `${name}: t at the read`).current = fact;
      const read = must(fn.expressions.find(e => e.pos[0] === ret + "return ".length && e.pos[1] === ret + "return t.mapping".length),
        `${name}: the read's claim`);
      read.type = must(fact.find(([[field]]) => field === "mapping"), `${name}: the mapping's fact`)[1];
      const input = writeClaims(artifacts, `forged-field-tag-${name}`, claims);
      const produce = produceWith(artifacts, input, `forged-field-tag-${name}`);
      assert.ifError(produce.error);
      assert.equal(produce.status, 1, produce.stdout + produce.stderr);
      for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)])
        assert.match(detail, /reject: source (incoming edge obligation|expression obligation|evidence does not justify|evidence refusal at)/);
    }
  }
  process.stdout.write("forged field tag facts, of a record's field and of a dictionary's entry: claimed before the test, past an aliasing write and past a call, refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A field's equality test is a fact of the field only where an edge
  // establishes it: claimed at the test, before it, the write of the field's
  // read past the test is refused where evidence is produced and where it is
  // checked.
  const artifacts = run("field-equality-union");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const fn = must(claims.functions.find(f => f.name === "kindOf"), "kindOf's claims");
  const from = source.indexOf("function kindOf");
  const test = must(fn.entries.find(e => e.start === source.indexOf("if (c.kind", from)), "the entry of the test");
  const past = must(fn.entries.find(e => e.start === source.indexOf("mode = c.kind", from)), "the entry past the test");
  must(test.bindings.find(b => b.name === "c"), "c at the test").current =
    must(past.bindings.find(b => b.name === "c"), "c past the test").current;
  const input = writeClaims(artifacts, "forged-field-equality-before", claims);
  const produce = produceWith(artifacts, input, "forged-field-equality-before");
  assert.ifError(produce.error);
  assert.equal(produce.status, 1, produce.stdout + produce.stderr);
  for (const detail of [produce.stdout + produce.stderr, invoke(input, join(artifacts, "evidence.json"), artifacts)])
    assert.match(detail, /reject: source (incoming edge obligation|expression obligation|evidence does not justify|evidence refusal at)/);
  process.stdout.write("forged field equality fact: claimed before the test refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A guard declaration claims the footprint its body stays within, as a
  // plain declaration does: claimed narrower, it is refused at the
  // declaration, where evidence is produced and where the honest evidence is
  // checked against the forged claim.
  for (const [file, name, consumed] of [["guard-footprint", "isText", true]] as const) {
    const artifacts = run(file);
    const claims = readClaims(artifacts);
    const guard = must(claims.functions.find(f => f.name === name), `${name}'s claims`);
    assert.notDeepEqual(guard.footprint, emptyFootprint, `${name}: its honest footprint`);
    guard.footprint = emptyFootprint;
    const input = writeClaims(artifacts, `forged-guard-effect-${name}`, claims);
    const refusal = `the footprint claimed for '${guard.name}' is not established by its body`;
    refusedAt(artifacts, input, `forged-guard-effect-${name}`, refusal);
    if (consumed) assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts).includes(refusal));
  }
  process.stdout.write("forged guard effects: a guard claimed within the empty footprint refused at the declaration, in search and in checking\n");
});

control(async (): Promise<void> => {
  // Certified imports: an import is read at its unit's footprint only where
  // the importer's claims list the read qualified, the module's claims are
  // about the module's bytes, the two readings of the unit's signature agree
  // and the module's own run is certified. Each forgery bypasses the producer
  // and is refused where evidence is produced and where the honest evidence
  // is checked.
  const imported = run("certified-value-import");
  const writing = run("invalid-certified-write-value-import");
  const refuse = (artifacts: string, name: string, claims: SourceClaims, refusal: RegExp,
      ast = join(artifacts, "fragment.json"), checked = refusal): void => {
    const input = writeClaims(artifacts, name, claims);
    const searched = produceWith(artifacts, input, name, ast);
    assert.ifError(searched.error);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.match(searched.stdout + searched.stderr, refusal);
    assert.match(invoke(input, join(artifacts, "evidence.json"), artifacts, ast), checked);
  };
  // A unit claimed within the empty footprint whose body pushes onto its
  // array: its module's run refuses it.
  const narrowed = readClaims(imported);
  const tally = must(narrowed.modules.flatMap(m => m.functions).find(f => f.name === "tally"), "tally's claims");
  assert.notDeepEqual(tally.footprint, emptyFootprint, "tally: its honest footprint");
  tally.footprint = emptyFootprint;
  refuse(imported, "forged-certified-footprint", narrowed,
    /module \.\/certified\.ts: .*the footprint claimed for 'tally' is not established by its body/s);
  assert.deepEqual(readClaims(writing).qualified.map(q => q.name), ["drop"], "drop is read qualified");
  // The importer's claims without their qualified reads: the imports are
  // read at their declared types, and the dense results are refused.
  const unqualified = readClaims(imported);
  assert.equal(unqualified.qualified.length, 5, "twice, label, tally, unwrap and unwrapped are read qualified");
  unqualified.qualified = [];
  // The honest evidence states its typings at the qualified signatures, which
  // the importer's document no longer has.
  refuse(imported, "forged-certified-unqualified", unqualified, /reject: source expression obligation/,
    join(imported, "fragment.json"), /reject: .*application of unknown head/);
  // A module's claims about other bytes.
  const stale = readClaims(imported);
  for (const m of stale.modules) m.sourceSha256 = "0".repeat(64);
  refuse(imported, "forged-certified-sha", stale, /a module's claims are about other bytes: \.\/certified\.ts/);
  // A qualified read closing a cycle: `pong`'s claims read `ping`, whose
  // claims read `pong`.
  const cycle = run("certified-cycle-value-import");
  const cyclic = readClaims(cycle);
  const pong = must(cyclic.modules.find(m => m.file === "./pong.ts"), "pong's claims");
  assert.deepEqual(pong.qualified, [], "pong reads ping at its ordinary signature");
  pong.qualified = cyclic.qualified.filter(q => q.name === "ping");
  assert.equal(pong.qualified.length, 1, "the importer reads ping qualified");
  refuse(cycle, "forged-certified-cycle", cyclic, /module \.\/p[io]ng\.ts: a cycle of qualified reads through it/);
  // A module document whose unit `twice` takes a string: the two readings of
  // its signature differ.
  const fragment: Ast = readFragmentFile(join(imported, "fragment.json"));
  const twice = must(fragment.modules.flatMap(m => m.functions).find(f => f.name === "twice"), "the module's twice");
  const param = must(twice.params[0], "twice's parameter");
  assert.ok(param.type.k === "atom" && param.type.name === "number", "twice takes a number");
  param.type = { ...param.type, name: "string" };
  const tampered = join(imported, "forged-certified-module.fragment.json");
  writeFileSync(tampered, JSON.stringify(fragment));
  refuse(imported, "forged-certified-module", readClaims(imported),
    /certified import \.\/certified\.ts#twice: the importer's and the module's readings of an imported signature differ/,
    tampered);
  // A module document stating `twice` async: its claimed footprint below
  // `top` is refused, read from the module's own document.
  const asyncModule: Ast = readFragmentFile(join(imported, "fragment.json"));
  const asyncTwice = must(asyncModule.modules.flatMap(m => m.functions).find(f => f.name === "twice"), "the module's twice");
  assert.equal(asyncTwice.completion, "sync", "twice is synchronous");
  asyncTwice.completion = "async";
  const asynced = join(imported, "forged-certified-async.fragment.json");
  writeFileSync(asynced, JSON.stringify(asyncModule));
  refuse(imported, "forged-certified-async", readClaims(imported),
    /(a qualified read names an async unit claimed below `top`: \.\/certified\.ts#twice|the footprint claimed for 'twice' is not `top`, and an async definition's is)/,
    asynced);
  // A module document in which `label` writes the binding of `twice`: the
  // binding is not stable, and the read of `twice` is refused.
  const rebinding: Ast = readFragmentFile(join(imported, "fragment.json"));
  const label = must(rebinding.modules.flatMap(m => m.functions).find(f => f.name === "label"), "the module's label");
  const pos = label.namePos;
  label.body.unshift({ k: "effect", pos, e: { k: "assign", pos, name: "twice", namePos: pos, rhs: { k: "id", pos, name: "label" } } });
  const rebound = join(imported, "forged-certified-rebinding.fragment.json");
  writeFileSync(rebound, JSON.stringify(rebinding));
  refuse(imported, "forged-certified-rebinding", readClaims(imported),
    /certified import \.\/certified\.ts#twice: a qualified read names a unit whose module writes its binding/, rebound);
  // A module document whose `ArrayProto` lacks a member the importer's has:
  // `tally`'s array parameter reads it implicitly, and the readings differ.
  const prototype: Ast = readFragmentFile(join(imported, "fragment.json"));
  const proto = must(must(prototype.modules.find(m => m.location === "./certified.ts"), "the module").declarations
    .definitions.find(d => d.declaration.name === "ArrayProto"), "the module's ArrayProto");
  const members = proto.expression?.k === "object" ? proto.expression.fields : [];
  assert.ok(members.length > 0, "ArrayProto's members");
  members.pop();
  const shortened = join(imported, "forged-certified-prototype.fragment.json");
  writeFileSync(shortened, JSON.stringify(prototype));
  refuse(imported, "forged-certified-prototype", readClaims(imported),
    /certified import \.\/certified\.ts#tally: the importer's and the module's readings of a declaration differ: .*ArrayProto/,
    shortened);
  // A module document whose written application in `unwrap`'s signature
  // states another bound: the readings of the application differ.
  const bounded: Ast = readFragmentFile(join(imported, "fragment.json"));
  const application = must(must(bounded.modules.find(m => m.location === "./certified.ts"), "the module").declarations
    .applications.find(a => a.site === "./certified.ts#unwrap"), "unwrap's written application");
  const bound = must(application.bounds[0], "Bounded's bound");
  assert.ok(bound.k === "atom" && bound.name === "number", "Bounded's bound is number");
  application.bounds = [{ ...bound, name: "unknown" }];
  const rebounded = join(imported, "forged-certified-application.fragment.json");
  writeFileSync(rebounded, JSON.stringify(bounded));
  refuse(imported, "forged-certified-application", readClaims(imported),
    /certified import \.\/certified\.ts#unwrap: the importer's and the module's readings of the written applications in \.\/certified\.ts#unwrap differ/,
    rebounded);
  // Readings of `twice` whose parameter is a scheme with a
  // resolution-qualified binder, alike in both, whose domain lowering takes
  // relative to `%Stable%` and native `Promise` (no reference in the term
  // names either). Refused where the module's document lacks `%Stable%` the
  // importer's states, and where both state `%Stable%` or `Promise` under
  // one identity and the definitions differ.
  const resolvable: Ast = readFragmentFile(join(run("generic-promise-resolvable"), "fragment.json"));
  const intrinsic = (name: string): TypeDefinition =>
    must(resolvable.declarations.definitions.find(d => d.declaration.name === name), `${name}'s definition`);
  const qualifiedScheme = (): Ast => {
    const doc: Ast = readFragmentFile(join(imported, "fragment.json"));
    const value = must(doc.declarations.values.find(v => v.declaration.name === "twice"), "twice's value");
    const unit = must(doc.modules.flatMap(m => m.functions).find(f => f.name === "twice"), "the unit twice");
    if (value.type.k !== "function") assert.fail("twice's value is a function");
    const signature = structuredClone(value.type);
    const scheme = (): TypeTerm => ({ k: "scheme", span: [0, 0], signatures: [structuredClone(signature)],
      binders: [{ name: "X", bound: null, resolution: { observation: "X#observed", result: "X#result" },
        default: null, span: [0, 0] }] });
    must(value.type.params[0], "twice's parameter");
    value.type.params[0] = scheme();
    must(unit.params[0], "the unit's parameter").type = scheme();
    return doc;
  };
  const moduleOf = (doc: Ast) => must(doc.modules.find(m => m.location === "./certified.ts"), "the module").declarations;
  const resolutionControls: [string, (doc: Ast) => void, RegExp][] = [
    ["lacking", (doc) => { moduleOf(doc).definitions.push(intrinsic("%Stable%")); },
      /a declaration one reading of an imported signature reads implicitly and the other lacks: .*stable/],
    ["stable", (doc) => {
      doc.declarations.definitions.push(intrinsic("%Stable%"));
      moduleOf(doc).definitions.push({ ...intrinsic("%Stable%"), expression: { k: "atom", name: "unknown", span: [0, 0] } });
    }, /the importer's and the module's readings of a declaration differ: .*%Stable%/],
    ["promise", (doc) => {
      doc.declarations.definitions.push(intrinsic("Promise"));
      const promise = structuredClone(intrinsic("Promise"));
      if (promise.expression?.k === "object") promise.expression.fields.pop();
      else assert.fail("Promise's definition is an object type");
      moduleOf(doc).definitions.push(promise);
    }, /the importer's and the module's readings of a declaration differ: .*"Promise"/],
  ];
  for (const [name, forge, refusal] of resolutionControls) {
    const doc = qualifiedScheme();
    forge(doc);
    const path = join(imported, `forged-certified-resolution-${name}.fragment.json`);
    writeFileSync(path, JSON.stringify(doc));
    refuse(imported, `forged-certified-resolution-${name}`, readClaims(imported),
      new RegExp(`certified import \\./certified\\.ts#twice: ${refusal.source}`), path);
  }
  process.stdout.write("forged certified imports: a narrowed unit, dropped qualified reads, stale module claims, a cycle of qualified reads, a differing module signature, a module prototype lacking a member, under a nested resolution-qualified binder a `%Stable%` one reading lacks, a differing `%Stable%` and a differing native `Promise`, a differing written application, a rebound unit and an async unit claimed below `top` refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // An element write is within `{value: any, store: keep}` at a required
  // position of its store's tuple contract, and within
  // `{value: any, store: grow}` elsewhere: `setSecond` writes a pair's second
  // position, `setThird` a triple's optional one. Claimed `keep` at the
  // required position, the claims are certified; claimed `keep` at the
  // optional one, or the empty footprint at the required one, refused where
  // evidence is produced and where the honest evidence is checked.
  const artifacts = run("map-stable-element-write");
  const forge = (name: string, footprint: ClosedFootprint): string => {
    const claims = readClaims(artifacts);
    must(claims.functions.find(f => f.name === name), `${name}'s claims`).footprint = footprint;
    return writeClaims(artifacts, `forged-element-write-${name}-${footprint.value}-${footprint.store}`, claims);
  };
  const kept = forge("setSecond", { value: "any", store: "keep" });
  const accepted = produceWith(artifacts, kept, "forged-element-write-kept");
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const checked = tested(verifierCall(verifier, ["--check-source-claims", join(artifacts, "fragment.json"), kept,
    sourceKey(artifacts), join(artifacts, "forged-element-write-kept-evidence.json")]));
  assert.equal(checked.status, 0, checked.stdout + checked.stderr);
  for (const [name, footprint] of [["setThird", { value: "any", store: "keep" }],
      ["setSecond", emptyFootprint]] as const) {
    const input = forge(name, footprint);
    const refusal = `the footprint claimed for '${name}' is not established by its body`;
    refusedAt(artifacts, input, `forged-element-write-${name}`, refusal);
    assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts).includes(refusal));
  }
  process.stdout.write("element writes: keep at a required position certified in search and checking, keep at an optional one and the empty footprint refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A negated guard as `||`'s left operand: where `!isRecord(v)` decides,
  // the outcome is the literal `true` at the span of the `!`, and there the
  // guard answered `false`. Claimed `false` at that span, or `v` claimed at
  // the guarded type where the condition throws, the claims are refused
  // where evidence is produced and where the honest evidence is checked.
  const artifacts = run("guard-negated-short-circuit");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const from = source.indexOf("function bounded");
  const bang = source.indexOf("!isRecord(v) || n > 3", from);
  const forge = (name: string, edit: (fn: SourceClaims["functions"][number]) => void): string => {
    const claims = readClaims(artifacts);
    edit(must(claims.functions.find(f => f.name === "bounded"), "bounded's claims"));
    return writeClaims(artifacts, name, claims);
  };
  const decided = forge("forged-negated-decided", fn => {
    const mark = must(fn.expressions.find(e => e.pos[0] === bang && e.pos[1] === bang + 1), "the decided outcome's claim");
    assert.deepEqual(mark.type, [1], "the decided outcome is true");
    mark.type = [2];
  });
  const thrown = forge("forged-negated-throw", fn => {
    const ret = must(fn.entries.find(e => e.start === source.indexOf("return v", from)), "the return's entry");
    const throwing = must(fn.entries.find(e => e.start === source.indexOf("throw Error", from)), "the throw's entry");
    must(throwing.bindings.find(b => b.name === "v"), "v at the throw").type =
      must(ret.bindings.find(b => b.name === "v"), "v at the return").type;
  });
  for (const [input, name, refusal] of [
    [decided, "forged-negated-decided", `source expression obligation at [${bang},${bang + 1}): evidence search failed: no derivation of its node-typing claim`],
    [thrown, "forged-negated-throw", "the edge from node"]] as const) {
    refusedAt(artifacts, input, name, refusal);
    // Checking the honest evidence refuses at a node of `bounded`, whose
    // claim the evidence states otherwise.
    const checked = invoke(input, join(artifacts, "evidence.json"), artifacts);
    const located = must(/source evidence refusal at \[(\d+),(\d+)\)/.exec(checked), checked);
    assert.ok(Number(located[1]) >= from, checked);
  }
  process.stdout.write("negated guard dispatch: a decided outcome claimed false and a narrowed claim where the guard answered false refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A guard's Boolean return is a condition returning the literal `true` at
  // the first code unit of its `return` and `false` at the second. Claimed
  // `false` where it returns `true`, the claims are refused where evidence
  // is produced and where the honest evidence is checked.
  const artifacts = run("guard-boolean-return");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "isFields"), "isFields' claims");
  const at = source.indexOf("return typeof v");
  const truth = must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === at + 1), "the true return's claim");
  assert.deepEqual(truth.type, [1], "the true return is true");
  truth.type = [2];
  const input = writeClaims(artifacts, "forged-boolean-return", claims);
  refusedAt(artifacts, input, "forged-boolean-return", `obligation at [${at},${at + 1})`);
  assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts)
    .includes(`reject: source evidence refusal at [${at},${at + 1}): the evidence does not establish this node's claim`));
  // The false return claimed `true`, and an arrow guard's true return, at
  // its `=>`, claimed `false`: each refused the same way.
  for (const [file, name, from, text, before, after] of [
    ["guard-boolean-return", "isFields", "function isFields", "return typeof v", 2, 1],
    ["guard-boolean-return-boundaries", "guardOf", "function guardOf", "=> typeof v", 1, 2],
  ] as const) {
    const where = run(file);
    const text0 = readFileSync(sourceKey(where), "utf8");
    const forgedClaims = readClaims(where);
    const fnClaims = must(forgedClaims.functions.find(f => f.name === name), `${name}'s claims`);
    const offset = text0.indexOf(text, text0.indexOf(from)) + (before === 2 ? 1 : 0);
    // A closure's interior claims are stated per signature row as well.
    const literals = [...fnClaims.expressions, ...(fnClaims.arrows ?? []).flatMap(a => a.rows.flatMap(r => r.expressions))]
      .filter(e => e.pos[0] === offset && e.pos[1] === offset + 1);
    assert.ok(literals.length > 0, `${name}'s literal at ${offset}`);
    for (const literal of literals) {
      assert.deepEqual(literal.type, [before], `${name}'s literal`);
      literal.type = [after];
    }
    const forgedInput = writeClaims(where, `forged-boolean-return-${name}`, forgedClaims);
    refusedAt(where, forgedInput, `forged-boolean-return-${name}`, "evidence search failed");
    assert.match(invoke(forgedInput, join(where, "evidence.json"), where),
      /reject: source evidence (does not justify the extracted program and exact claims|refusal at \[\d+,\d+\): the evidence does not establish this (node|obligation)'s claim)/);
  }
  process.stdout.write("guard Boolean return: the true return claimed false, the false one claimed true and an arrow's true one claimed false refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A guard closure passed as a callback is claimed at its own signature,
  // its promise and the callback's longer signature. Claimed without the
  // promise, the closure is refused where evidence is produced and where the
  // honest evidence is checked.
  const artifacts = run("guard-closure-callback");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const fn = must(claims.functions.find(f => f.name === "allPresent"), "allPresent's claims");
  const at = source.indexOf("(x): x is string");
  const closure = must(fn.expressions.find(e => e.pos[0] === at), "the closure's claim");
  const label = Array.isArray(closure.type) ? closure.type[0] : undefined;
  assert.ok(typeof label === "number", "the closure's claim is a row");
  const row = must(claims.types[label], "the closure's row");
  const clause = row[0];
  assert.ok(clause !== undefined && typeof clause === "object" && "arrs" in clause, "an arrow clause");
  const arrows = clause.arrs.arrows;
  const promised = arrows.findIndex(a => a.effect.promise !== null);
  assert.ok(promised >= 0, "the claim offers the promise");
  arrows.splice(promised, 1);
  const rows = must((fn.arrows ?? []).find(a => a.pos[0] === at), "the closure's arrow rows");
  rows.rows.splice(promised, 1);
  const input = writeClaims(artifacts, "forged-guard-closure-promise", claims);
  const refusal = "a guard closure's claim must offer its written promise over its annotated parameters";
  refusedAt(artifacts, input, "forged-guard-closure-promise", refusal);
  assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts).includes(refusal));
  // The callback's longer signature, a row of its own, claimed at a result
  // the body does not return, and the rows of interior claims one short of
  // the signatures: each refused where evidence is produced and where the
  // honest evidence is checked.
  type ClosureArrows = Extract<SourceClaims["types"][number][number], { arrs: unknown }>["arrs"]["arrows"];
  type ClosureRows = NonNullable<SourceClaims["functions"][number]["arrows"]>[number]["rows"];
  const forgeLonger = (name: string, edit: (forgedArrows: ClosureArrows, forgedRows: ClosureRows) => void): string => {
    const forged = readClaims(artifacts);
    const forgedFn = must(forged.functions.find(f => f.name === "allPresent"), "allPresent's claims");
    const forgedClosure = must(forgedFn.expressions.find(e => e.pos[0] === at), "the closure's claim");
    const forgedLabel = Array.isArray(forgedClosure.type) ? forgedClosure.type[0] : undefined;
    assert.ok(typeof forgedLabel === "number", "the closure's claim is a row");
    const forgedClause = must(forged.types[forgedLabel], "the closure's row")[0];
    assert.ok(forgedClause !== undefined && typeof forgedClause === "object" && "arrs" in forgedClause, "an arrow clause");
    edit(forgedClause.arrs.arrows, must((forgedFn.arrows ?? []).find(a => a.pos[0] === at), "the closure's rows").rows);
    return writeClaims(artifacts, name, forged);
  };
  const longerResult = forgeLonger("forged-guard-closure-longer-result", (arrows) => {
    const longer = must(arrows.find(a => a.arguments.length > 1), "the callback's longer signature");
    longer.result = [rowOf(claims, "nul")];
  });
  const shortRows = forgeLonger("forged-guard-closure-short-rows", (_, rows) => { rows.pop(); });
  for (const [input, name, refusal] of [
    [longerResult, "forged-guard-closure-longer-result", "reject: "],
    [shortRows, "forged-guard-closure-short-rows", "per-arrow interior claims do not match the claimed arrows"],
  ] as const) {
    const searched = produceWith(artifacts, input, name);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.ok((searched.stdout + searched.stderr).includes(refusal), searched.stdout + searched.stderr);
    assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts).includes(refusal));
  }
  process.stdout.write("guard closure callback: a claim without the promise, a longer row at an unjustified result and rows short of the signatures refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A guard closure passed to `filter` is claimed at the guard overload's
  // longer promise signature (`offer-promise`), the one the call is checked
  // at. That row forged without its promise, at a promise the body does not
  // establish, at a parameter outside the closure's contextual one, or at a
  // footprint narrower than the top one a promise row's code is checked at:
  // each refused where evidence is produced and where the honest evidence is
  // checked.
  const artifacts = run("filter-guard-callback");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const at = source.indexOf("(d): d is Declaration => d.kind === \"declaration\")");
  assert.ok(at >= 0, "the guard closure of `declarations`");
  type ClosureArrow = Extract<SourceClaims["types"][number][number], { arrs: unknown }>["arrs"]["arrows"][number];
  const forgeLonger = (name: string, edit: (longer: ClosureArrow, claims: SourceClaims) => void): string => {
    const forged = readClaims(artifacts);
    const fn = must(forged.functions.find(f => f.name === "declarations"), "declarations' claims");
    const closure = must(fn.expressions.find(e => e.pos[0] === at), "the closure's claim");
    const label = Array.isArray(closure.type) ? closure.type[0] : undefined;
    assert.ok(typeof label === "number", "the closure's claim is a row");
    const clause = must(forged.types[label], "the closure's row")[0];
    assert.ok(clause !== undefined && typeof clause === "object" && "arrs" in clause, "an arrow clause");
    const longer = must(clause.arrs.arrows.find(a => a.arguments.length > 1 && a.effect.promise !== null),
      "the longer promise signature");
    edit(longer, forged);
    return writeClaims(artifacts, name, forged);
  };
  const forgeries = [
    [forgeLonger("forged-filter-guard-plain", (longer) => { longer.effect = { ...longer.effect, promise: null }; }), "forged-filter-guard-plain", "reject: "],
    [forgeLonger("forged-filter-guard-promise", (longer, claims) => { longer.result = [rowOf(claims, "nul")]; }),
      "forged-filter-guard-promise", "reject: "],
    [forgeLonger("forged-filter-guard-parameter", (longer, claims) => { longer.arguments[0] = [rowOf(claims, "nul")]; }),
      "forged-filter-guard-parameter", "closure signature claim is outside the source annotation"],
    [forgeLonger("forged-filter-guard-footprint", (longer) => { longer.effect = { ...longer.effect, footprint: { value: "keep", store: "keep" } }; }),
      "forged-filter-guard-footprint", "reject: "],
  ] as const;
  for (const [input, name, refusal] of forgeries) {
    const searched = produceWith(artifacts, input, name);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.ok((searched.stdout + searched.stderr).includes(refusal), searched.stdout + searched.stderr);
    assert.ok(invoke(input, join(artifacts, "evidence.json"), artifacts).includes(refusal));
  }
  process.stdout.write("filter guard closure: its longer promise signature without the promise, at an unestablished promise, a parameter outside its context and a narrower footprint refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // A footprint check that runs out of subtype rounds is inconclusive, not a
  // refusal: `marks` claims the empty footprint, and with one round the
  // checks of its graph exhaust. Search and checking report exhaustion, never
  // a footprint refusal.
  const file = join(here, "examples", "declaration-preserving-callback.ts");
  const searched = check(file, undefined, false, 1);
  assert.equal(searched.status, "exhausted", JSON.stringify(searched));
  const artifacts = run("declaration-preserving-callback");
  const checking = tested(verifierCall(verifier, ["--subtype-rounds", "1", "--check-source-claims",
    join(artifacts, "fragment.json"), join(artifacts, "claims.json"), sourceKey(artifacts),
    join(artifacts, "evidence.json")]));
  assert.equal(checking.status, 1, checking.stdout + checking.stderr);
  const failure = readDiagnostic(checking.stdout + checking.stderr);
  assert.ok(failure && failure.outcome.kind === "exhausted", checking.stdout + checking.stderr);
  assert.doesNotMatch(checking.stdout + checking.stderr, /source effect refusal/);
  process.stdout.write("exhausted footprint check: reported as exhausted in search and in checking\n");
});

control(async (): Promise<void> => {
  // A footprint and an effect have one spelling: `grow` on a value, which
  // is `keep` there, and an effect without its promise field are refused
  // where the claims are read.
  const artifacts = run("optional-call-loop-cell");
  const evidence = join(artifacts, "evidence.json");
  const claims = readClaims(artifacts);
  const collect = must(claims.functions.find(f => f.name === "collect"), "collect's claims");
  const grown = join(artifacts, "forged-footprint-value-grow.json");
  writeFileSync(grown, must(JSON.stringify(claims, (key, value: unknown) =>
    key === "footprint" && value === collect.footprint ? { value: "grow", store: "keep" } : value), "the forged claims' text"));
  assert.match(invoke(grown, evidence, artifacts), /invalid footprint change 'grow'/);
  const arrow = must(claims.types.flatMap(row => row.flatMap(clause =>
    typeof clause === "object" && "arrs" in clause ? clause.arrs.arrows : []))[0], "a claimed arrow");
  const unpromised = join(artifacts, "forged-effect-without-promise.json");
  writeFileSync(unpromised, must(JSON.stringify(claims, (key, value: unknown) =>
    key === "effect" && value === arrow.effect ? { footprint: arrow.effect.footprint } : value), "the forged claims' text"));
  assert.match(invoke(unpromised, evidence, artifacts), /promise/);
  process.stdout.write("footprints and effects other than the one spelling: refused\n");
});

control(async (): Promise<void> => {
  // An imported function is read at its declaration's type, which states no
  // effect: its call claimed at any narrower footprint, with the callback
  // through it, is refused.
  const artifacts = run("invalid-preserving-callback-value-import");
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

/** Bypass the producer's refusal: propose claims over a parser document
 * weakened by `change`, then require search over those claims against the
 * honest document to refuse at the obligation located at `at`, and checking
 * to refuse the evidence searched over the weakened document. That evidence
 * is over another graph, so checking refuses it unlocated. */
const bypassed = (artifacts: string, name: string, at: [number, number], change: (fragment: Ast) => void): void => {
  const ast: Ast = readFragmentFile(join(artifacts, "fragment.json"));
  change(ast);
  const weak = join(artifacts, `${name}-fragment.json`);
  writeFileSync(weak, JSON.stringify(ast));
  const lowered = tested(verifierCall(verifier, ["--lower-control-flow", weak]));
  assert.equal(lowered.status, 0, lowered.stderr);
  const flow = join(artifacts, `${name}-flow.json`);
  writeFileSync(flow, lowered.stdout);
  const proposal = tested(producerCall(producerExecutable, [weak, flow]));
  assert.equal(proposal.status, 0, proposal.stderr);
  const claims = join(artifacts, `${name}-claims.json`);
  writeFileSync(claims, proposal.stdout);
  const made = produceWith(artifacts, claims, name, weak);
  assert.equal(made.status, 0, made.stdout + made.stderr);
  refusedAt(artifacts, claims, `${name}-honest`, `obligation at [${at[0]},${at[1]})`);
  invoke(claims, join(artifacts, `${name}-evidence.json`), artifacts);
};
/** A verified case's operand claim at `operand`, of a record whose field `a`
 * is a number, weakened to `{ readonly a: number }`, which admits a host
 * object. The entry contracts stay honest; search must refuse at the
 * operation spanning the first `operation`, and checking of the honest
 * evidence within it. */
const weakenedOperand = (file: string, name: string, operation: string, operand: string): void => {
  const artifacts = run(file);
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const op = source.indexOf(operation);
  assert.ok(op >= 0, `${file}: ${operation}`);
  const start = op + operation.indexOf(operand);
  const claim = must(claims.functions.flatMap(f => f.expressions)
    .find(e => e.pos[0] === start && e.pos[1] === start + operand.length), `${file}: the claim of ${operand}`);
  claim.type = [rowOf(claims, { refs: { first: [], rest: [], views: [["a", [rowOf(claims, "num")]]] } })];
  const input = writeClaims(artifacts, name, claims);
  const at = `[${op},${op + operation.length})`;
  refusedAt(artifacts, input, name, `obligation at ${at}`);
  // Checking the honest evidence refuses within the operation: at it, or at
  // an obligation of its operands, whose evidence states the honest claim.
  const checked = invoke(input, join(artifacts, "evidence.json"), artifacts);
  const located = must(/source evidence refusal at \[(\d+),(\d+)\)/.exec(checked), checked);
  assert.ok(op <= Number(located[1]) && Number(located[2]) <= op + operation.length, checked);
};

control(async (): Promise<void> => {
  // The non-host parameter of `Object.values` and a merge's operands
  // (COMPILER-API.md, "Restricted values"): an argument claimed at a record of
  // readonly fields alone, which admits a host object, is refused at the
  // call, and a spread's operand so claimed at the merge, in search and in
  // checking the honest evidence.
  weakenedOperand("host-exclusion-reflection", "forged-non-host-argument", "Object.values(o)", "o");
  weakenedOperand("host-exclusion-merges", "forged-non-host-spread", "{ ...o }", "o");
  process.stdout.write("forged host-admitting operands: an argument and a spread operand claimed at readonly fields refused at the call and the merge, in search and in checking\n");
});

control(async (): Promise<void> => {
  // A recursive closure's self entry is at the closure's own claimed type,
  // which its code must establish (SOURCE-ELABORATION.md, "Recursive constants"):
  // the claim forged to a result its body does not return, or to a footprint
  // its body exceeds, is refused in search and in checking the honest
  // evidence, within the closure.
  const artifacts = run("recursive-constants");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  for (const [name, label] of [["depth", "result"], ["writes", "footprint"]] as const) {
    const claims = readClaims(artifacts);
    const start = source.indexOf("const visit = ", source.indexOf(`function ${name}(`)) + "const visit = ".length;
    // The literal's claim: the longest claim starting at it.
    const claim = must(claims.functions.flatMap(f => f.expressions).filter(e => e.pos[0] === start)
      .sort((a, b) => b.pos[1] - a.pos[1])[0], `${name}: the literal's claim`);
    assert.ok(Array.isArray(claim.type));
    const rows = claim.type.map(l => must(typeof l === "number" ? claims.types[l] : undefined, "a row"));
    claim.type = rows.map(row => claims.types.push(row.map(clause => {
      if (typeof clause !== "object" || !("arrs" in clause)) return clause;
      const arrows = clause.arrs.arrows.map(a => {
        const copy = structuredClone(a);
        if (label === "result") copy.result = [rowOf(claims, "str")];
        else copy.effect = footprintEffect(keepAll);
        return copy;
      });
      return { arrs: { ...clause.arrs, arrows } };
    })) - 1);
    const input = writeClaims(artifacts, `forged-self-${label}`, claims);
    const searched = produceWith(artifacts, input, `forged-self-${label}`);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    const checked = invoke(input, join(artifacts, "evidence.json"), artifacts);
    // Search refuses within the function. Checking the honest evidence
    // refuses there or in a later unit: with the forged row in use, the
    // honest certificate of a later unit claiming a footprint no longer
    // establishes it (an unused forged row changes nothing), and footprint
    // refusals are reported before node refusals.
    const body = source.indexOf(`function ${name}(`);
    for (const [detail, within] of [[searched.stdout + searched.stderr, true], [checked, false]] as const) {
      const at = must(/(?:obligation|refusal) at \[(\d+),(\d+)\)/.exec(detail), detail);
      assert.ok(Number(at[1]) >= body && (!within || Number(at[2]) <= source.indexOf("\n}\n", body) + 2), detail);
    }
  }
  process.stdout.write("forged recursive closures: a self type at a result and at a footprint the body does not establish refused in search and in checking\n");
});

control(async (): Promise<void> => {
  // Reading rule 1 on a stand-in host package (`pipeline/host-fixture/`,
  // whose `Node` reaches no node list), activated by the compiler API's
  // description naming the stand-in's installation and digest: the shape
  // omits the allocating `jsDoc`, so every form of its read is refused, and
  // reads of other members verify. The stand-in declares no `tokenCache`, so
  // the description omits `jsDoc` alone.
  const project = tsconfigOf(join(import.meta.dirname, "host-fixture-project"));
  const example = (file: string): string => join(import.meta.dirname, "examples", `${file}.ts`);
  useFamiliesForTests([{ ...compilerApiFamily, installation: { from: "pipeline/host-fixture-project",
    digest: "9d2da7d1428fb185d589e2d72425e34dd96dacebafb443d2c8c37202424bb3da" },
    omitted: compilerApiFamily.omitted.filter(m => m.member === "jsDoc") }]);
  try {
    for (const [form, refusal] of [
      ["dot", /missing field jsDoc/], ["element", /missing field jsDoc/], ["paren-key", /missing field jsDoc/],
      ["const-key", /missing field jsDoc/], ["template-key", /dynamic index requires a dictionary over its keys/],
      ["binding", /missing field jsDoc/], ["optional", /missing field jsDoc/],
      ["view", /no derivation of its binding-annotation claim/],
    ] as const) {
      const outcome = check(example(`invalid-host-fixture-jsdoc-${form}`), project);
      assert.notEqual(outcome.status, "verified", `invalid-host-fixture-jsdoc-${form}: refused`);
      assert.ok("detail" in outcome && refusal.test(outcome.detail), `invalid-host-fixture-jsdoc-${form}: ${JSON.stringify(outcome)}`);
    }
    // Recovering the omitted member: the parser's document given `jsDoc` back
    // on the host `Node`, the claims and evidence so made refused against the
    // honest document, whose shape omits it.
    const dot = check(example("invalid-host-fixture-jsdoc-dot"), project);
    const read = readFileSync(sourceKey(dot.artifacts), "utf8").indexOf("n.jsDoc");
    bypassed(dot.artifacts, "forged-host-jsdoc", [read, read + "n.jsDoc".length], fragment => {
      const definition = must(fragment.declarations?.definitions.find(d => d.declaration.name === "Node"), "the host Node");
      assert(definition.expression?.k === "object");
      const kind = must(definition.expression.fields.find(f => f.name === "kind"), "Node's kind");
      definition.expression.fields.push({ ...kind, name: "jsDoc", optional: true, type: { k: "atom", name: "unknown", span: kind.span } });
    });
    // Node lists: read as dense readonly arrays; their own members unread.
    const rows = check(example("host-fixture-node-list"), project);
    assert.equal(rows.status, "verified", JSON.stringify(rows));
    const written = check(example("invalid-host-fixture-node-list-write"), project);
    assert.ok(written.status !== "verified" && "detail" in written && /transformFlags/.test(written.detail),
      JSON.stringify(written));
    // Branded strings (reading rule 5): read as strings, refused as a host
    // parameter (L5).
    const branded = check(example("host-fixture-branded-read"), project);
    assert.equal(branded.status, "verified", JSON.stringify(branded));
    for (const [file, refusal] of [
      ["invalid-host-fixture-branded-parameter", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-callback-result", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-held", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-argument", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-nested", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-curried", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-optional-parameter", /branded string Path where the client would produce one/],
      ["invalid-host-fixture-branded-return", /the intersection is empty/],
      ["invalid-host-fixture-branded-alias", /the intersection is empty/],
    ] as const) {
      const refused = check(example(file), project);
      assert.ok(refused.status !== "verified" && "detail" in refused && refusal.test(refused.detail),
        `${file}: ${JSON.stringify(refused)}`);
    }
    for (const file of ["host-fixture-branded-callback", "host-fixture-branded-positions"]) {
      const supplied = check(example(file), project);
      assert.equal(supplied.status, "verified", `${file}: ${JSON.stringify(supplied)}`);
    }
    // A member declared `any`: optional, of type `unknown` (reading rule 2).
    const brand = check(example("host-fixture-brand-optional"), project);
    assert.equal(brand.status, "verified", JSON.stringify(brand));
    const required = check(example("invalid-host-fixture-brand-required"), project);
    assert.ok(required.status === "unverified" && /No rule derives this invoke/.test(required.detail),
      JSON.stringify(required));
    const kept = check(example("host-fixture-jsdoc-other-reads"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    const lookalike = check(example("host-fixture-lookalike"), project);
    assert.equal(lookalike.status, "unsupported", JSON.stringify(lookalike));
  } finally {
    useFamiliesForTests(null);
  }
  process.stdout.write("host reading on a stand-in host: every read of jsDoc refused, also with claims made over a document stating it; other reads verified; a node list read as a dense readonly array, its members unread; a branded string read as a string where the host produces it, refused where the client would; a member declared any optional\n");
});

control(async (): Promise<void> => {
  // A test of a readonly view narrows a union by the arms whose view answers
  // it: the read of `o` after `o.k === "a"` forged to the arm whose `k` is
  // "b" is refused, the edge's field slice keeping only the "a" arm.
  const artifacts = run("readonly-view-narrowing");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const measure = must(claims.functions.find((f) => f.name === "measure"), "measure's claims");
  const at = source.indexOf("o.x");
  const read = must(measure.expressions.find((e) => e.pos[0] === at && e.pos[1] === at + 1), "the read of o on the true edge");
  const other = must(measure.expressions.find((e) => e.pos[0] === source.indexOf("o.y") && e.pos[1] === source.indexOf("o.y") + 1),
    "the read of o on the false edge");
  read.type = other.type;
  const forged = writeClaims(artifacts, "forged-view-narrowing", claims);
  const searched = produceWith(artifacts, forged, "forged-view-narrowing");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /evidence search failed/);
  process.stdout.write("forged view narrowing: the other arm on the true edge refused\n");
});

control(async (): Promise<void> => {
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
  const source = readFileSync(sourceKey(artifacts), "utf8");
  // The answers' literals at the first two code units of the `return`
  // (`booleanReturn`) keep their claims.
  const answer = (e: { pos: [number, number] }): boolean =>
    source.startsWith("return", e.pos[0]) || source.startsWith("eturn", e.pos[0]);
  const read = must(guard.expressions.find((e) => !answer(e) && source.slice(e.pos[0], e.pos[1]) === x.name),
    "the read of the argument");
  for (const e of guard.expressions) if (!answer(e)) e.type = e === read ? [str] : [tru];
  const forged = writeClaims(artifacts, "forged-guard-promise", claims);
  const searched = produceWith(artifacts, forged, "forged-guard-promise");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /source incoming edge obligation at \[271,300\): evidence search failed/);
  process.stdout.write("forged guard promise: refused at the guard's body\n");
});

control(async (): Promise<void> => {
  // A call narrows its argument by the promise the parser's document states
  // of its callee, never by the producer's claims: with the promise removed
  // from `isPresence`'s document, the producer's claims, which read
  // `isPresence` at its qualified signature, are refused at that read.
  const artifacts = run("type-guards");
  const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
  const isPresence = must(fragment.functions.find((f) => f.name === "isPresence"), "isPresence");
  assert.ok(isPresence.guard, "isPresence states a promise");
  isPresence.guard = null;
  const ast = join(artifacts, "forged-unpromised-guard.json");
  writeFileSync(ast, JSON.stringify(fragment));
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-unpromised-guard", ast);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const call = source.indexOf("isPresence(v)");
  assert.match(searched.stdout + searched.stderr,
    new RegExp(`source expression obligation at \\[${call},${call + "isPresence".length}\\): evidence search failed`));
  assert.match(invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, ast), /obligation|evidence|claim/);
  process.stdout.write("unpromised guard call: its qualified read refused\n");
});

control(async (): Promise<void> => {
  // A closure's written promise is proved whatever the claims offer: with
  // the promise signature removed from the arrow constant `isNumber`'s claim,
  // and its body's claims for that signature, the closure is refused.
  const artifacts = run("type-guards");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});

control(async (): Promise<void> => {
  // A closure's written promise is about every input its annotation admits:
  // with `isNumber`'s promise signature claimed at the parameter `number`,
  // where it holds of every argument, the closure is refused.
  const artifacts = run("type-guards");
  const claims = readClaims(artifacts);
  const source = readFileSync(sourceKey(artifacts), "utf8");
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
});
control(async (): Promise<void> => {
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
});
control(async (): Promise<void> => {
  // A tag set has one spelling: its elements sorted and distinct, at least
  // two (HOST-FAMILIES.md, "Tag sets"). Claims spelling a set otherwise are
  // refused by the decoder.
  const artifacts = run("tag-sets");
  const original = readClaims(artifacts);
  const numbers = original.types.findIndex((row) => row.length === 1 && typeof row[0] === "object" && "numIn" in row[0]);
  const strings = original.types.findIndex((row) => row.length === 1 && typeof row[0] === "object" && "strIn" in row[0]);
  assert.ok(numbers >= 0 && strings >= 0, "the claims state a number set and a string set");
  const forgeries: [string, number, (bits: string[]) => string[], RegExp][] = [
    ["unsorted-number-set", numbers, (xs) => [...xs].reverse(), /a number set lists two or more bit patterns, sorted and distinct/],
    ["duplicate-number-set", numbers, (xs) => [xs[0] ?? "0", ...xs], /a number set lists two or more bit patterns, sorted and distinct/],
    ["single-number-set", numbers, (xs) => xs.slice(0, 1), /a number set lists two or more bit patterns, sorted and distinct/],
    ["unsorted-string-set", strings, (xs) => [...xs].reverse(), /a string set lists two or more strings, sorted and distinct/],
    ["single-string-set", strings, (xs) => xs.slice(0, 1), /a string set lists two or more strings, sorted and distinct/],
  ];
  for (const [name, row, forge, refusal] of forgeries) {
    const claims = readClaims(artifacts);
    const clause = claims.types[row]?.[0];
    if (typeof clause === "object" && "numIn" in clause) clause.numIn.bits = forge(clause.numIn.bits);
    else if (typeof clause === "object" && "strIn" in clause) clause.strIn.values = forge(clause.strIn.values);
    else assert.fail("the forged row is a tag set");
    const forged = writeClaims(artifacts, `forged-${name}`, claims);
    const searched = produceWith(artifacts, forged, `forged-${name}`);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.match(searched.stdout + searched.stderr, refusal);
  }
  process.stdout.write("forged tag sets: unsorted, duplicated and single-element sets refused\n");
});
control(async (): Promise<void> => {
  // A residual arm is no shape (HOST-FAMILIES.md, "Residuals"): claims
  // stating the node a kind test's false edge leaves at the shape the test
  // excluded, and its `parent` then at `Node`, bypass the producer and are
  // refused by the search.
  const artifacts = run("invalid-compiler-api-residual-parent");
  const text = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const expressions = must(claims.functions[0], "up's claims").expressions;
  const at = (start: number, length: number) =>
    must(expressions.find((e) => e.pos[0] === start && e.pos[1] === start + length), `the claim at ${start}`);
  const shape = at(text.lastIndexOf("return n;") + "return ".length, 1).type;
  const parent = text.lastIndexOf("n.parent");
  at(parent, 1).type = shape;
  const read = at(parent, "n.parent".length);
  const labels = read.type;
  assert.ok(Array.isArray(labels), "n.parent is claimed at labels");
  read.type = labels.filter((label) => typeof label === "object");
  const forged = writeClaims(artifacts, "forged-residual-shape", claims);
  refusedAt(artifacts, forged, "forged-residual-shape", `at [${parent},${parent + 1})`);
  process.stdout.write("forged residual claims: the node a kind test's false edge leaves claimed at the excluded shape, refused\n");
});
control(async (): Promise<void> => {
  // Forged claims of family readings bypassing the producer, refused in
  // search and in checking against the case's own evidence: the node a
  // kind test's false edge leaves claimed at the shape that test excluded,
  // and a program allocation claimed at a family type, which it cannot meet
  // since no program allocation owns the marker (HOST-FAMILIES.md, "The
  // family contract", "Activation").
  // Each forgery returns the position of the claim it forges; the refusal
  // names an obligation whose span holds it.
  type Unit = NonNullable<SourceClaims["init"]>;
  const forgeries: [string, string, string, (text: string, function_: Unit) => number][] = [
    ["forged-excluded-arm", "compiler-api-kind-narrowing", "fileName", (text, f) => {
      const at = (start: number) => must(f.expressions.find((e) => e.pos[0] === start && e.pos[1] === start + 1), `the claim at ${start}`);
      const excluded = text.indexOf("n.fileName");
      const read = text.lastIndexOf("n.text");
      at(read).type = at(excluded).type;
      return read;
    }],
    // A guard's false edge (HOST-FAMILIES.md, "Calls"): the argument
    // claimed at the shape its true edge leaves, which every input reaching
    // the false edge contradicts.
    ["forged-guard-false-edge", "compiler-api-guard-false-branch", "count", (text, f) => {
      const at = (start: number) => must(f.expressions.find((e) => e.pos[0] === start && e.pos[1] === start + "node".length), `the claim at ${start}`);
      const read = text.lastIndexOf("node.elements");
      at(read).type = at(text.indexOf("node.text")).type;
      return read;
    }],
    // A guard value's promise (HOST-FAMILIES.md, "Guards as values"): where
    // a call of a name holding it answers `true`, the argument claimed at
    // what its `false` answer leaves, which excludes every input answering
    // `true`.
    ["forged-guard-value-promise", "compiler-api-guard-values", "stored", (text, f) => {
      const at = (start: number) => must(f.expressions.find((e) => e.pos[0] === start && e.pos[1] === start + "node".length), `the claim at ${start}`);
      const read = text.indexOf("node.text", text.indexOf("g(node)"));
      at(read).type = at(text.indexOf("node.pos", read)).type;
      return read;
    }],
    ["forged-family-member", "compiler-api-family-identity", "held", (text, f) => {
      const literal = text.indexOf("{ node: n }");
      const node = text.indexOf("n }", literal);
      const claim = must(f.expressions.find((e) => e.pos[0] === literal && e.pos[1] === literal + "{ node: n }".length), "the literal's claim");
      claim.type = must(f.expressions.find((e) => e.pos[0] === node && e.pos[1] === node + 1), "the node's claim").type;
      return literal;
    }],
    // Family identity through program code (HOST-FAMILIES.md, "Identity
    // through program code"), each claim at the identifier shape the
    // case's own guard gives: a callback of `forEachChild` returning the
    // node it received, at a node type it did not receive; the node on the
    // `false` edge of a guard a program module re-exports; and the node
    // where a wrapper of a guard answers `true`, which the wrapper's own
    // `boolean` does not narrow.
    ["forged-callback-result", "compiler-api-node-callback", "%init%", (text, f) => {
      const returned = text.indexOf("=> c;") + "=> ".length;
      const interior = [...f.expressions, ...(f.arrows ?? []).flatMap((a) => a.rows.flatMap((r) => r.expressions))];
      must(interior.find((e) => e.pos[0] === returned && e.pos[1] === returned + 1), "the callback's result").type =
        identifierShape(text, "n.text");
      return returned;
    }],
    ["forged-reexported-false-edge", "compiler-api-guard-calls", "reexportedOther", (text, f) => {
      const read = text.indexOf("n.pos", text.indexOf("function reexportedOther"));
      must(f.expressions.find((e) => e.pos[0] === read && e.pos[1] === read + 1), "the false edge's node").type =
        identifierShape(text, "n.text");
      return read;
    }],
    ["forged-guard-wrapper", "compiler-api-guard-calls", "wrappedRead", (text, f) => {
      const read = text.indexOf("n.pos", text.indexOf("function wrappedRead"));
      must(f.expressions.find((e) => e.pos[0] === read && e.pos[1] === read + 1), "the wrapper's node").type =
        identifierShape(text, "n.text");
      return read;
    }],
  ];
  // The claim of the node a guard's `true` edge reads at `read`, the first
  // of the case: the identifier shape, by its label in the claims document.
  let shapes: SourceClaims | null = null;
  const identifierShape = (text: string, read: string): SourceClaims["functions"][number]["expressions"][number]["type"] => {
    const at = text.indexOf(read);
    const found = must(shapes, "the case's claims").functions.flatMap((f) => f.expressions)
      .find((e) => e.pos[0] === at && e.pos[1] === at + 1);
    return must(found, `the claim of the node at ${read}`).type;
  };
  const locatedAt = (detail: string, position: number): boolean =>
    [...detail.matchAll(/at \[(\d+),(\d+)\)/g)].some((m) => Number(m[1]) <= position && position < Number(m[2]));
  for (const [name, file, function_, forge] of forgeries) {
    const artifacts = run(file);
    const text = readFileSync(sourceKey(artifacts), "utf8");
    const claims = readClaims(artifacts);
    shapes = claims;
    const unit: Unit = function_ === "%init%" ? must(claims.init, "the initialization claims")
      : must(claims.functions.find((f) => f.name === function_), `${function_}'s claims`);
    const position = forge(text, unit);
    const forged = writeClaims(artifacts, name, claims);
    const searched = produceWith(artifacts, forged, name);
    const detail = searched.stdout + searched.stderr;
    assert.equal(searched.status, 1, detail);
    assert.ok(/evidence search failed/.test(detail) && locatedAt(detail, position), `${name}: refused at the forged claim: ${detail}`);
    // The case's evidence, offered for the forged claims, is refused: the
    // checker names the first node whose evidence does not establish its
    // claim, or the evidence as a whole, not the forged claim. The guards'
    // own rules are reached by forged evidence (below).
    assert.match(invoke(forged, join(artifacts, "evidence.json"), artifacts),
      /evidence does not justify the extracted program and exact claims|evidence refusal at \[\d+,\d+\)/);
  }
  process.stdout.write("forged family claims: the excluded arm on a kind test's and on a guard's false edge, a guard value's promise at the shapes it excludes, a program allocation at a family type, a forEachChild callback's result at a node type it did not receive, the false edge of a re-exported guard and the node a guard's wrapper answers true of, each at the identifier shape, refused by the search at the forged claim and by the checker against the case's evidence\n");
});
control(async (): Promise<void> => {
  // Forged evidence of a guard's false entailments, offered with the case's
  // own claims, so that only the forged yields differ and the checker's
  // refusal is the yield's rule, located at the guard's call: a membership
  // test's `false` edge stating the argument at what its `true` edge leaves
  // (`member-yield`), and a guard value's promise stating that no argument
  // answers `true` (`promise-call`).
  type Certificate = { yields: { conditional: boolean; onFalse: boolean; target: number; type: unknown }[] }[];
  const isObject = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
  const forgeries: [string, string, string, string, (certificate: Certificate) => void][] = [
    ["forged-member-false-yield", "compiler-api-guard-false-branch", "count", "ts.isIdentifier(node)", (certificate) => {
      for (const node of certificate)
        for (const y of node.yields)
          if (y.onFalse) y.type = must(node.yields.find((z) => !z.onFalse && z.target === y.target), "the true edge's yield").type;
    }],
    ["forged-promise-yield", "compiler-api-guard-values", "stored", "g(node)", (certificate) => {
      for (const node of certificate) for (const y of node.yields) if (y.conditional) y.type = [];
    }],
  ];
  for (const [name, file, function_, call, forge] of forgeries) {
    const artifacts = run(file);
    const text = readFileSync(sourceKey(artifacts), "utf8");
    const index = readClaims(artifacts).functions.findIndex((f) => f.name === function_);
    const evidence: unknown = JSON.parse(readFileSync(join(artifacts, "evidence.json"), "utf8"));
    assert.ok(isObject(evidence) && isObject(evidence.main) && Array.isArray(evidence.main.functions), "the case's evidence");
    const unit: unknown = evidence.main.functions[index];
    assert.ok(isObject(unit) && Array.isArray(unit.certificate), `${function_}'s certificate`);
    const before = JSON.stringify(unit.certificate);
    forge(unit.certificate as Certificate); // asserted: a certificate of the case's evidence, decoded by Lean; the forgery writes yields only
    assert.notEqual(JSON.stringify(unit.certificate), before, `${name}: a yield forged`);
    const path = join(artifacts, `${name}-evidence.json`);
    writeFileSync(path, JSON.stringify(evidence));
    const start = text.indexOf(call);
    assert.ok(start >= 0, `${name}: the call`);
    assert.match(invoke(join(artifacts, "claims.json"), path, artifacts),
      new RegExp(`^reject: source evidence refusal at \\[${start},${start + call.length}\\): the evidence does not establish this node's typing`),
      `${name}: refused at the guard's call`);
  }
  process.stdout.write("forged guard evidence: a membership test's false edge at its true edge's slice, and a guard value's promise excluding every true answer, refused by the checker at the guard's call\n");
});
control(async (): Promise<void> => {
  // The domain obligation (HOST-FAMILIES.md, "Calls"): a parser document
  // stating a guard's call at a domain its argument's claim is not within
  // (`never`), with the entry's tags and with none, is refused at the call
  // by Lean's `guard-domain` obligation, whatever the producer claims: in
  // search, and by the checker against the case's evidence, whose proof of
  // the obligation at the reviewed domain is the only part that differs.
  // The calls: a condition the executable lowering tests
  // (`compiler-api-guard-false-branch`), a callback's body
  // (`compiler-api-guard-values`), and a negated condition, which the
  // closure lowering also plans, each plan stating the obligation
  // (`compiler-api-guards`; without the executable lowering's obligation,
  // only this call's forged domain is refused). One stating no domain is
  // refused by the decoder.
  const isObject = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
  const calls: [string, string][] = [
    ["compiler-api-guard-false-branch", "ts.isIdentifier(node)"],
    ["compiler-api-guard-values", "ts.isIdentifier(n)"],
    ["compiler-api-guards", "isStringLiteral(node)"],
  ];
  for (const [file, text] of calls) {
    const artifacts = run(file);
    const start = readFileSync(sourceKey(artifacts), "utf8").indexOf(text);
    const document: unknown = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
    const found: Record<string, unknown>[] = [];
    const visit = (v: unknown): void => {
      if (Array.isArray(v)) v.forEach(visit);
      else if (isObject(v)) {
        if (v.k === "tagMember" && Array.isArray(v.pos) && v.pos[0] === start) found.push(v);
        Object.values(v).forEach(visit);
      }
    };
    visit(document);
    const [call] = found;
    assert.ok(call && found.length === 1 && Array.isArray(call.pos), `${file}: the guard's call ${text}`);
    const { domain, tags } = call;
    const forgedDocument = (name: string, replaced: unknown, replacedTags: unknown): string => {
      call.domain = replaced;
      call.tags = replacedTags;
      const path = join(artifacts, `${name}.fragment.json`);
      writeFileSync(path, JSON.stringify(document) ?? "");
      call.domain = domain;
      call.tags = tags;
      return path;
    };
    const claims = join(artifacts, "claims.json");
    const at = `at [${call.pos.join(",")})`;
    const never = { k: "atom", name: "never", span: call.pos };
    const variants: [string, unknown][] = [["entry", tags], ["empty", []]];
    for (const [variant, replacedTags] of variants) {
      const name = `forged-guard-domain-${variant}`;
      const narrowed = forgedDocument(name, never, replacedTags);
      const searched = produceWith(artifacts, claims, name, narrowed);
      const detail = searched.stdout + searched.stderr;
      assert.equal(searched.status, 1, detail);
      assert.ok(detail.includes(at), `${file}, ${variant} tags: the narrowed domain refused at the call in search: ${detail}`);
      assert.ok(invoke(claims, join(artifacts, "evidence.json"), artifacts, narrowed).startsWith(
        `reject: source evidence refusal ${at}: the evidence does not establish this obligation's claim`),
        `${file}, ${variant} tags: the narrowed domain refused at the call by the checker`);
    }
    const absent = produceWith(artifacts, claims, "forged-guard-no-domain", forgedDocument("forged-guard-no-domain", null, tags));
    assert.equal(absent.status, 1, absent.stdout + absent.stderr);
    assert.match(absent.stdout + absent.stderr, /a family guard's call states its guard's domain/);
  }
  process.stdout.write("forged guard domains: a domain the argument is not within, with the entry's tags and with none, in a condition, a callback's body and a negated condition, refused at the call by the search and by the checker against the case's evidence; a call without its domain by the decoder\n");
});
// A guard binds by what Node loads for the client's own import
// (HOST-FAMILIES.md, "Calls"). A project whose `paths` point TypeScript at
// the audited declarations, beside a `node_modules/typescript` Node loads:
// a link to the audited installation, whose `isIdentifier` is the checked
// function, narrows; a copy of the package, another instance of the same
// code, is no guard. One control for each.
for (const copy of [false, true]) control(async (): Promise<void> => {
  const installation = resolve(import.meta.dirname, "..", "tools", "node_modules", "typescript");
  const nested = (name: string, place: (target: string) => void): Outcome => {
    const dir = runDirectory(`tscert-nested-${name}-`);
    writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
      module: "preserve", moduleResolution: "bundler", target: "es2022", verbatimModuleSyntax: true, types: [],
      paths: { "typescript/unstable/ast": [join(installation, "dist", "ast", "index.d.ts")] } }, include: ["*.ts"] }));
    const source = join(dir, "name.ts");
    writeFileSync(source, 'import * as ts from "typescript/unstable/ast";\n\n' +
      "export function name(n: ts.Node): string {\n  return ts.isIdentifier(n) ? n.text : \"\";\n}\n");
    mkdirSync(join(dir, "node_modules"));
    place(join(dir, "node_modules", "typescript"));
    return check(source, tsconfigOf(dir));
  };
  if (!copy) {
    const linked = nested("linked", (target) => symlinkSync(installation, target));
    assert.equal(linked.status, "verified", JSON.stringify(linked));
    process.stdout.write("nested installations: the audited package linked narrows\n");
  } else {
    const copied = nested("copied", (target) => cpSync(installation, target, { recursive: true, dereference: true }));
    assert.ok(copied.status === "unsupported" && copied.detail.includes("missing field text"), JSON.stringify(copied));
    process.stdout.write("nested installations: a copy of the audited package in the client's node_modules is no guard\n");
  }
});
control(async (): Promise<void> => {
  // F5 (HOST-FAMILIES.md, "Trust rows"): the package's enum objects are never
  // written. Claims bypassing the producer that read `ts.SyntaxKind` at the
  // writable record its alias is bound to are refused by the search at that
  // read: the enum object's type is its declaration's, whatever is claimed.
  const artifacts = run("invalid-compiler-api-enum-field-write");
  const text = readFileSync(sourceKey(artifacts), "utf8");
  const claims = readClaims(artifacts);
  const expressions = must(claims.functions[0], "rewrite's claims").expressions;
  const at = (start: number, length: number) =>
    must(expressions.find((e) => e.pos[0] === start && e.pos[1] === start + length), `the claim at ${start}`);
  const read = text.indexOf("ts.SyntaxKind;");
  at(read, "ts.SyntaxKind".length).type = at(text.indexOf("kinds.Identifier"), "kinds".length).type;
  const forged = writeClaims(artifacts, "forged-enum-writable-alias", claims);
  refusedAt(artifacts, forged, "forged-enum-writable-alias", `at [${read},${read + "ts.SyntaxKind".length})`);
  process.stdout.write("forged enum claims: the tag enum read at a writable record, refused at the read\n");
});
control(async (): Promise<void> => {
  // An enum's reverse keys (SOURCE-CONTRACTS.md, "Enums"), by claims
  // bypassing the producer. The key of a read at the enum's values, claimed
  // at `number`, which it meets, leaves the read at an arbitrary number:
  // refused, the object stating a reverse key at its values alone.
  const artifacts = run("enum-reverse-keys");
  const text = readFileSync(sourceKey(artifacts), "utf8");
  const read = text.indexOf("Open[k]");
  {
    const claims = readClaims(artifacts);
    const key = must(claims.functions.find((f) => f.name === "openName"), "openName's claims").expressions
      .find((e) => e.pos[0] === read + "Open[".length);
    must(key, "the claim of the key").type = [rowOf(claims, "num")];
    const forged = writeClaims(artifacts, "forged-enum-reverse-number", claims);
    const searched = produceWith(artifacts, forged, "forged-enum-reverse-number");
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.match(searched.stdout + searched.stderr, /a numeric array key needs a proved array-index singleton/);
  }
  // An ambient enum's object states its members alone. The claims of the
  // same source reading a constant declared with a reverse key, `Grede`,
  // stated of the ambient enum `Grade`'s read, are refused at that read.
  const refused = run("invalid-ambient-enum-reverse");
  const source = readFileSync(sourceKey(refused), "utf8");
  const dir = runDirectory("tscert-ambient-reverse-");
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true, target: "es2022" },
    include: ["*.ts"] }));
  const shadowed = join(dir, "shadowed.ts");
  writeFileSync(shadowed, source.replace("return Grade[0]", "return Grede[0]"));
  const kept = check(shadowed, tsconfigOf(dir));
  assert.equal(kept.status, "verified", JSON.stringify(kept));
  const claims = { ...readClaims(kept.artifacts), file: sourceKey(refused),
    sourceSha256: createHash("sha256").update(source).digest("hex") };
  const at = source.indexOf("Grade[0]");
  refusedAt(refused, writeClaims(refused, "forged-ambient-enum-reverse", claims),
    "forged-ambient-enum-reverse", `at [${at},${at + "Grade".length})`);
  process.stdout.write("forged enum reverse claims: a key at number, and an ambient enum's reverse key, refused\n");
});
control(async (): Promise<void> => {
  // A correction of a method to absent (HOST-FAMILIES.md, "The family
  // contract"): under a description correcting `getText` at one tag, the
  // method is an optional member of every reading covering that tag, the
  // tag's own shape, a generic declaration applied at any of its tags, a
  // selected generic arm and a residual holding the tag, so each call is
  // refused at its read; under the compiler API's own description each
  // verifies.
  const project = tsconfigOf(join(import.meta.dirname, "compiler-api-project"));
  const getText = (kind: string) => ({ kind, owner: "Node", member: "getText", text: "getText(sourceFile?: SourceFile): string;" });
  const controls = [
    ["SourceFile", "compiler-api-corrected-method", "f.getText"],
    ["SourceFile", "compiler-api-corrected-residual", "n.getText"],
    ["QuestionToken", "compiler-api-corrected-token", "t.getText"],
    ["QuestionToken", "compiler-api-corrected-arm", "n.getText"],
    ["QuestionToken", "compiler-api-corrected-residual", "n.getText"],
  ] as const;
  // The claims and evidence of a run under the compiler API's own
  // description, offered with the corrected declaration document as if the
  // producer had proposed them. The two documents name the same
  // definitions in the same order, every method's definition written
  // whether or not a reading shares it, so the claims and the evidence keep
  // their meaning; offered with the plain document they are accepted.
  const located = (detail: string, position: number): boolean =>
    [...detail.matchAll(/at \[(\d+),(\d+)\)/g)].some((m) => Number(m[1]) <= position && position < Number(m[2]));
  const verifierOn = (fragment: string, claims: string, source: string, evidence: string): Invoked =>
    tested(verifierCall(verifier, ["--check-source-claims", fragment, claims, source, evidence]), 60_000);
  const plainRuns = new Map<string, string>();
  for (const name of new Set(controls.map(([, file]) => file))) {
    const plain = check(join(import.meta.dirname, "examples", `${name}.ts`), project);
    assert.equal(plain.status, "verified", `${name}: ${JSON.stringify(plain)}`);
    plainRuns.set(name, plain.artifacts);
  }
  for (const [kind, name, read] of controls) {
    useFamiliesForTests([{ ...compilerApiFamily, corrections: [...compilerApiFamily.corrections, getText(kind)] }]);
    let artifacts: string;
    try {
      const file = join(import.meta.dirname, "examples", `${name}.ts`);
      const corrected = check(file, project);
      const at = readFileSync(file, "utf8").indexOf(read);
      // The producer finds no arrow to call in a possibly absent member, or
      // no member in a residual that forgets it, at the read.
      assert.ok(corrected.status === "unsupported" && corrected.detail.includes(`at [${at},`) &&
        /call requires a single arrow the arguments can call|missing field getText/.test(corrected.detail),
        `${name} with getText corrected at ${kind}: refused at ${read}: ${JSON.stringify(corrected)}`);
      artifacts = corrected.artifacts;
    } finally {
      useFamiliesForTests(null);
    }
    const plain = must(plainRuns.get(name), "the plain run");
    const identities = (dir: string): string[] => must(readFragmentFile(join(dir, "fragment.json")).declarations, "the declarations")
      .definitions.map((d) => JSON.stringify(d.declaration));
    assert.deepEqual(identities(artifacts), identities(plain), `${name}: both documents name the same definitions in order`);
    const at = readFileSync(sourceKey(artifacts), "utf8").indexOf(read);
    // Accepted with the plain document, refused with the corrected one: by
    // the search at the read, and by the checker at the call.
    const accepted = verifierOn(join(plain, "fragment.json"), join(plain, "claims.json"), sourceKey(plain), join(plain, "evidence.json"));
    assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
    const fragment = readFragmentFile(join(artifacts, "fragment.json"));
    const forged = join(artifacts, "forged-corrected.json");
    const claims: unknown = JSON.parse(readFileSync(join(plain, "claims.json"), "utf8"));
    assert.ok(typeof claims === "object" && claims !== null);
    writeFileSync(forged, JSON.stringify({ ...claims, file: fragment.file }));
    const searched = produceWith(artifacts, forged, "forged-corrected");
    assert.ok(searched.status === 1 && located(searched.stdout + searched.stderr, at),
      `${name} at ${kind}: the search refuses at ${read}: ${searched.stdout + searched.stderr}`);
    const checked = verifierOn(join(artifacts, "fragment.json"), forged, sourceKey(artifacts), join(plain, "evidence.json"));
    assert.ok(checked.status === 1 && located(checked.stdout + checked.stderr, at),
      `${name} at ${kind}: the checker refuses at ${read}: ${checked.stdout + checked.stderr}`);
  }
  process.stdout.write("corrected method: a method a correction makes absent at a tag is optional in that tag's shape, a generic declaration and a selected generic arm, and forgotten in a residual: each call refused by the producer at it, and claims made under the plain description refused by Lean's search at the read and by its checker\n");
});
control(async (): Promise<void> => {
  // A method declared optional (HOST-FAMILIES.md, "The family contract"):
  // on a stand-in host package whose family root declares `describe?()`
  // beside `text()`, each shape names the shared definition of `text` as a
  // base and states `describe` as its own optional member, and its call is
  // refused at the call.
  const project = tsconfigOf(join(import.meta.dirname, "family-fixture-project"));
  const example = (file: string): string => join(import.meta.dirname, "examples", `${file}.ts`);
  useFamiliesForTests([{ ...compilerApiFamily, installation: { from: "pipeline/family-fixture-project",
    digest: "aaaa66cf18b7f7d980c0e7734ae6421159ac2eccbbaa8d28b76f03e4280701ff" },
  table: [{ rule: "literal" }], corrections: [], omitted: [], footprints: [] }]);
  try {
    const kept = check(example("family-fixture-optional-method"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    const first = must(must(readFragmentFile(join(kept.artifacts, "fragment.json")).declarations, "the declarations")
      .definitions.find((d) => d.declaration.name === "First"), "First's reading");
    assert.deepEqual(first.bases.map((b) => b.k === "reference" ? b.reference.name : b.k), ["Node.text"]);
    assert.ok(first.expression?.k === "object" && first.expression.fields.some((f) => f.name === "describe" && f.optional),
      "First states describe optional");
    const file = example("invalid-family-fixture-optional-method");
    const refused = check(file, project);
    const at = readFileSync(file, "utf8").indexOf("n.describe");
    assert.ok(refused.status === "unsupported" && refused.detail.includes(`at [${at},`), JSON.stringify(refused));
  } finally {
    useFamiliesForTests(null);
  }
  process.stdout.write("declared-optional method: each shape's own optional member, the required one shared, its call refused\n");
});
control(async (): Promise<void> => {
  // A second family (HOST-FAMILIES.md, "Instances"): a stand-in package of
  // string-tagged units, activated beside the compiler API's by a
  // description of its own, which names the stand-in's package, its
  // installation and its digest, its tag `type`, a string, and a guard table
  // that activates over the stand-in's own modules. A guard of one tag and
  // one through a helper of its tag narrow both edges, each call a
  // membership test of the family's string constants; a guard whose answer
  // depends on an option argument has no entry and narrows nothing.
  const project = tsconfigOf(join(import.meta.dirname, "string-family-fixture-project"));
  const example = (file: string): string => join(import.meta.dirname, "string-family-fixture-project", `${file}.ts`);
  const strings: FamilyDescription = stringFamily;
  // The stand-in's description beside the compiler API's: the active
  // descriptions, the whole of what the run is given.
  const activate = (description: FamilyDescription): void => useFamiliesForTests([compilerApiFamily, description]);
  activate(strings);
  try {
    const kept = check(example("guards"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    const tagSets: string[] = [];
    const visit = (v: unknown): void => {
      if (Array.isArray(v)) v.forEach(visit);
      else if (typeof v === "object" && v !== null) {
        if ("k" in v && v.k === "tagMember" && "tags" in v) tagSets.push(JSON.stringify(v.tags) ?? "");
        Object.values(v).forEach(visit);
      }
    };
    visit(JSON.parse(readFileSync(join(kept.artifacts, "fragment.json"), "utf8")));
    assert.ok(tagSets.includes(JSON.stringify([{ a: "stringlit", v: "call" }, { a: "stringlit", v: "name" }]) ?? ""),
      `isExpression's call tests the family's string constants: ${tagSets.join(" ")}`);
    const file = example("invalid-loose");
    const refused = check(file, project);
    const at = readFileSync(file, "utf8").lastIndexOf("n.name");
    assert.ok(refused.status === "unsupported" && refused.detail.includes(`at [${at},`), JSON.stringify(refused));
    // The tag enum read as a value, by the description alone: its members
    // are the runtime object the activated entry point exports. Over a copy
    // whose `kinds.js` gives `Literal` another value, its guard table
    // activated over the copy's own digests, the same program is refused at
    // the read, and under Node `literalTag` returns the runtime value, not
    // its declared `"literal"`.
    const kinds = check(example("kinds"), project);
    assert.equal(kinds.status, "verified", JSON.stringify(kinds));
    // The compiler API's named views apply to its installation alone: the
    // stand-in's `Program` and `API`, of the views' names, are read by their
    // own declarations.
    const views = check(example("views"), project);
    assert.equal(views.status, "verified", JSON.stringify(views));
    {
      const copy = runDirectory("tscert-tag-enum-");
      const installed = join(copy, "node_modules", "string-family-fixture");
      mkdirSync(join(copy, "node_modules"));
      cpSync(join(import.meta.dirname, "string-family-fixture"), installed, { recursive: true });
      const runtime = readFileSync(join(installed, "kinds.js"), "utf8").replace('UnitType["Literal"] = "literal"', 'UnitType["Literal"] = "lit"');
      assert.ok(runtime.includes('"lit"'), "the copy's runtime enum differs");
      writeFileSync(join(installed, "kinds.js"), runtime);
      cpSync(join(import.meta.dirname, "string-family-fixture-project", "tsconfig.json"), join(copy, "tsconfig.json"));
      cpSync(example("kinds"), join(copy, "kinds.ts"));
      activate({ ...strings, installation: { ...strings.installation, from: copy },
        guards: { ...strings.guards, closure: { ...strings.guards.closure, files: { ...strings.guards.closure.files,
          "kinds.js": createHash("sha256").update(runtime).digest("hex") } } } });
      const mismatched = check(join(copy, "kinds.ts"), tsconfigOf(copy));
      assert.ok(mismatched.status === "unsupported" && /the host enum UnitType is not one .* nor a family's tag enum its runtime object matches/.test(mismatched.detail),
        JSON.stringify(mismatched));
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { literalTag } from ${JSON.stringify(pathToFileURL(join(copy, "kinds.ts")).href)};\nconsole.log(literalTag());\n`],
        { encoding: "utf8", cwd: copy });
      assert.equal(ran.stdout.trim(), "lit", `literalTag under Node: ${ran.stderr}`);
      activate(strings);
    }
    {
      // The tag enum's binding is the object activation checked, as Node
      // resolves the client's import: a project whose `paths` point
      // TypeScript at the stand-in's audited declarations while Node loads a
      // copy whose `Literal` is "lit" is refused at the read; with Node
      // loading the audited installation, the same program verifies.
      const bindingRun = (name: string, target: string, change: ((dir: string) => void) | null): { outcome: Outcome; dir: string } => {
        const dir = runDirectory(`tscert-tag-binding-${name}-`);
        writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
          module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
          paths: { "string-family-fixture/ast": [join(import.meta.dirname, "string-family-fixture", "ast.d.ts")] } }, include: ["*.ts"] }));
        mkdirSync(join(dir, "node_modules"));
        const installed = join(dir, "node_modules", "string-family-fixture");
        if (change) {
          cpSync(target, installed, { recursive: true });
          change(installed);
        } else symlinkSync(target, installed);
        cpSync(example("kinds"), join(dir, "kinds.ts"));
        return { outcome: check(join(dir, "kinds.ts"), tsconfigOf(dir)), dir };
      };
      const audited = bindingRun("audited", join(import.meta.dirname, "string-family-fixture"), null);
      assert.equal(audited.outcome.status, "verified", JSON.stringify(audited.outcome));
      const other = bindingRun("other", join(import.meta.dirname, "string-family-fixture"), (installed) => {
        const runtime = readFileSync(join(installed, "kinds.js"), "utf8").replace('UnitType["Literal"] = "literal"', 'UnitType["Literal"] = "lit"');
        writeFileSync(join(installed, "kinds.js"), runtime);
      });
      assert.ok(other.outcome.status === "unsupported" && /the host enum UnitType is not one .* nor a family's tag enum its runtime object matches/.test(other.outcome.detail),
        JSON.stringify(other.outcome));
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { literalTag } from ${JSON.stringify(pathToFileURL(join(other.dir, "kinds.ts")).href)};\nconsole.log(literalTag());\n`],
        { encoding: "utf8", cwd: other.dir });
      assert.equal(ran.stdout.trim(), "lit", `literalTag under Node, its import bound to the copy: ${ran.stderr}`);
    }
    {
      // Guard recognition stays within one family: a second family, a copy
      // of the stand-in under another name and marker whose `UnitType.Name`
      // is "nm", is active beside it, with guards and a domain of the same
      // names. A project whose `paths` point TypeScript at the stand-in's
      // declarations while Node binds `isName` to the copy's is no guard
      // call, refused at the return of the `false` edge's tag; with Node binding the
      // stand-in's, it verifies.
      const source = 'import { isName, type Unit } from "string-family-fixture/ast";\n\n' +
        'export function tagOf(n: Unit): "call" | "literal" | "" {\n  return isName(n) ? "" : n.type;\n}\n';
      const project = (name: string): string => {
        const dir = runDirectory(`tscert-guard-family-${name}-`);
        writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
          module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
          paths: { "string-family-fixture/ast": [join(import.meta.dirname, "string-family-fixture", "ast.d.ts")] } }, include: ["*.ts"] }));
        writeFileSync(join(dir, "tag-of.ts"), source);
        mkdirSync(join(dir, "node_modules"));
        return dir;
      };
      const same = project("same");
      symlinkSync(join(import.meta.dirname, "string-family-fixture"), join(same, "node_modules", "string-family-fixture"));
      const crossed = project("crossed");
      const copy = join(crossed, "node_modules", "string-family-fixture-b");
      cpSync(join(import.meta.dirname, "string-family-fixture"), copy, { recursive: true });
      const manifest: unknown = JSON.parse(readFileSync(join(copy, "package.json"), "utf8"));
      assert.ok(typeof manifest === "object" && manifest !== null);
      writeFileSync(join(copy, "package.json"), JSON.stringify({ ...manifest, name: "string-family-fixture-b" }));
      const kinds = readFileSync(join(copy, "kinds.js"), "utf8").replace('UnitType["Name"] = "name"', 'UnitType["Name"] = "nm"');
      writeFileSync(join(copy, "kinds.js"), kinds);
      symlinkSync(copy, join(crossed, "node_modules", "string-family-fixture"));
      const second: FamilyDescription = { ...strings, package: { ...strings.package, name: "string-family-fixture-b" },
        installation: { ...strings.installation, from: crossed }, marker: "StringFixtureB",
        guards: { ...structuredClone(strings.guards), closure: { ...strings.guards.closure, files: { ...strings.guards.closure.files,
          "kinds.js": createHash("sha256").update(kinds).digest("hex") } } } };
      useFamiliesForTests([compilerApiFamily, strings, second]);
      try {
        const verified = check(join(same, "tag-of.ts"), tsconfigOf(same));
        assert.equal(verified.status, "verified", JSON.stringify(verified));
        const refused = check(join(crossed, "tag-of.ts"), tsconfigOf(crossed));
        const returned = source.indexOf("isName(n) ?");
        assert.ok(refused.status !== "verified" && "detail" in refused && refused.detail.includes(`at [${returned},`) &&
          refused.detail.includes('"" | "call" | "literal" | "name"'), JSON.stringify(refused));
      } finally {
        activate(strings);
      }
      const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
        `import { tagOf } from ${JSON.stringify(pathToFileURL(join(crossed, "tag-of.ts")).href)};\nconsole.log(tagOf({ type: "name" }));\n`],
        { encoding: "utf8", cwd: crossed });
      assert.equal(ran.stdout.trim(), "name", `tagOf under Node, isName bound to the copy: ${ran.stderr}`);
    }
    // Activation fails closed: under a description whose digest differs from
    // the stand-in's declarations, or whose installation Node does not find,
    // the same program is refused; with no stand-in description its guards
    // narrow nothing.
    for (const [what, description, refusal] of [
      ["another digest", { ...strings, installation: { ...strings.installation, digest: "0".repeat(64) } },
        /is not the one the family StringFixture was reviewed against/],
      ["an installation Node does not find", { ...strings, installation: { ...strings.installation, from: "pipeline/host-fixture-project" } },
        /the family StringFixture's package string-family-fixture does not resolve from pipeline\/host-fixture-project/],
    ] as const) {
      activate(description);
      const closed = check(example("guards"), project);
      assert.ok(closed.status !== "verified" && "detail" in closed && refusal.test(closed.detail), `${what}: ${JSON.stringify(closed)}`);
    }
    useFamiliesForTests([compilerApiFamily]);
    const inactive = check(example("guards"), project);
    assert.ok(inactive.status !== "verified", `no stand-in description: ${JSON.stringify(inactive)}`);
    activate(strings);
    // Stable members through the same code (HOST-FAMILIES.md, "Stable
    // keys"): every property member of the stand-in is stable, so a callee
    // tested and read past a call is the tested value; the description
    // excluding `Call.callee`, the one thing changed, refuses the read.
    const stable = check(example("stable"), project);
    assert.equal(stable.status, "verified", JSON.stringify(stable));
    activate({ ...strings, stable: { excluded: [{ owner: "Call", member: "callee", text: "readonly callee: Unit;" }] } });
    const excluded = check(example("stable"), project);
    const read = readFileSync(example("stable"), "utf8").lastIndexOf("c.callee.name");
    assert.ok(excluded.status !== "verified" && excluded.detail.includes(`at [${read},`), JSON.stringify(excluded));
    // The tag's stability follows its declarations, a residual's too: with
    // `Literal.type` excluded, the residual standing for `Literal` states no
    // stable tag, while `Name`'s shape keeps its own.
    activate({ ...strings, stable: { excluded: [{ owner: "Literal", member: "type", text: "readonly type: UnitType.Literal;" }] } });
    const tagged = check(example("guards"), project);
    assert.equal(tagged.status, "verified", JSON.stringify(tagged));
    const shapes = must(readFragmentFile(join(tagged.artifacts, "fragment.json")).declarations, "the declarations").definitions
      .flatMap(d => d.expression?.k === "object" && d.expression.host !== undefined ? [{ name: d.declaration.name, term: d.expression }] : []);
    const residuals = shapes.filter(s => s.name.includes(" tags "));
    assert.ok(residuals.length > 0, "a residual arm");
    for (const r of residuals) assert.ok(!(r.term.stable ?? []).includes("type"), `${r.name}: no stable tag over an excluded one`);
    const name = must(shapes.find(s => s.name === "Name"), "the Name shape");
    assert.ok((name.term.stable ?? []).includes("type"), "Name's own tag stays stable");
    // An omitted member (HOST-FAMILIES.md, "The family contract"): the
    // description listing `Unit.notes`, the one thing changed, omits it from
    // every shape, so its read is refused; without the entry it verifies.
    activate(strings);
    const plain = check(example("notes"), project);
    assert.equal(plain.status, "verified", JSON.stringify(plain));
    activate({ ...strings, omitted: [{ owner: "Unit", member: "notes", text: "readonly notes: readonly string[];", why: "allocates" }] });
    const omitted = check(example("notes"), project);
    const notesAt = readFileSync(example("notes"), "utf8").lastIndexOf("u.notes");
    assert.ok(omitted.status !== "verified" && omitted.detail.includes(`at [${notesAt},`), JSON.stringify(omitted));
  } finally {
    useFamiliesForTests(null);
  }
  process.stdout.write("string-tagged family, activated by its description beside the compiler API's: its guards' calls are membership tests of string constants narrowing both edges, through a helper too; a guard outside the contract narrows nothing; its declarations of the compiler API's view names read as declared; its tag enum read as a value where its runtime object matches, refused over a copy whose runtime value differs and where Node binds the import to such a copy while TypeScript reads the audited declarations (Node returns it); a guard Node binds to another family's function, of the same name and domain, no guard (Node returns the excluded tag); a description of another digest or of an installation Node does not find refuses the run, and without the description nothing narrows; a stable member's test read past a call, refused where the description excludes the member; an excluded tag stable in no residual; an omitted member's read refused where the description lists it\n");
});
control(async (): Promise<void> => {
  // Guards on a value that may be `undefined` (HOST-FAMILIES.md, "Undefined
  // arguments"), over the stand-in family, whose table admits both kinds:
  // `isName`, a node guard, throws there, so its `false` edge holds a unit;
  // `isNameType`, a tag guard of equalities, answers `false`, so its `true`
  // edge holds the name's tag and its `false` edge keeps `undefined`,
  // returned where a tag is promised and refused; `isNameOrAbsent`, which
  // answers `true` there, has no entry and narrows nothing. Under Node each
  // refused function returns `undefined` where its result promises none.
  const dir = join(import.meta.dirname, "string-family-fixture-project");
  const project = tsconfigOf(dir);
  const example = (file: string): string => join(dir, `${file}.ts`);
  useFamiliesForTests([compilerApiFamily, stringFamily]);
  try {
    const kept = check(example("undefined"), project);
    assert.equal(kept.status, "verified", JSON.stringify(kept));
    // Bypassing the producer: `tagOrNone`'s `false` edge claimed to hold a
    // tag alone, where the guard answers `false` on `undefined`, is refused
    // by the search and by the checker with the honest run's evidence, at
    // the conditional, whose `false` edge from the guard's answer on
    // `undefined` establishes no such claim.
    const { artifacts } = kept;
    const text = readFileSync(example("undefined"), "utf8");
    const conditional = text.indexOf("isNameType(t) ? UnitType.Name : t");
    const at = text.indexOf(": t;", conditional) + 2;
    const claims = readClaims(artifacts);
    const read = must(claims.functions.find((f) => f.name === "tagOrNone")?.expressions
      .find((e) => e.pos[0] === at && e.pos[1] === at + 1), "the false edge's read of t");
    const absent = rowOf(claims, "undef");
    const honest = read.type;
    assert.ok(Array.isArray(honest) && honest.includes(absent), "the honest claim keeps undefined");
    read.type = honest.filter((l) => l !== absent);
    const forged = writeClaims(artifacts, "forged-guard-false-edge", claims);
    const edge = `at [${conditional},${at + 1})`;
    refusedAt(artifacts, forged, "forged-guard-false-edge", edge);
    assert.ok(invoke(forged, join(artifacts, "evidence.json"), artifacts).includes(edge));
    for (const [file, text] of [["invalid-undefined-false", "isNameType(t) ? UnitType.Name : t"],
        ["invalid-absent", "isNameOrAbsent(u) ? u : null"]] as const) {
      const refused = check(example(file), project);
      const at = readFileSync(example(file), "utf8").indexOf(text);
      assert.ok(refused.status === "unverified" && refused.detail.includes(`at [${at},`) &&
        refused.detail.includes("no derivation of its return-contract claim"), `${file}: ${JSON.stringify(refused)}`);
    }
  } finally {
    useFamiliesForTests(null);
  }
  const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
    `import { other } from ${JSON.stringify(pathToFileURL(example("invalid-undefined-false")).href)};\n` +
    `import { named } from ${JSON.stringify(pathToFileURL(example("invalid-absent")).href)};\n` +
    `import { unitStart } from ${JSON.stringify(pathToFileURL(example("undefined")).href)};\n` +
    `let threw = "";\ntry { unitStart(undefined); } catch (e) { threw = e instanceof TypeError ? "TypeError" : "other"; }\n` +
    `console.log(JSON.stringify([other(undefined), named(undefined), threw]));\n`],
    { encoding: "utf8", cwd: dir });
  assert.equal(ran.stdout.trim(), JSON.stringify([null, null, "TypeError"]), `under Node: ${ran.stderr}`);
  process.stdout.write("guards on undefined, over the stand-in family: a node guard's false edge holds a unit, a tag guard's true edge its tag; the tag guard's false edge keeps undefined, forged claims stating it present refused by the search and the checker, and a guard answering true on it has no entry, each refused at its return, where under Node it returns undefined; the node guard throws a TypeError on it\n");
});
control(async (): Promise<void> => {
  // A node guard on a `parent` that may be absent (HOST-FAMILIES.md,
  // "Undefined arguments"), its claims forged bypassing the producer, each
  // refused by the search and by the checker with the honest evidence:
  // `parent` claimed present in the handler of the guard's throw
  // (`handlerParent`), and the guard's argument claimed to hold a string
  // beside a node or `undefined` (`parentNamed`), which the domain
  // obligation on the dispatch's defined arm refuses at the call.
  const artifacts = run("compiler-api-guard-undefined");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const claimAt = (claims: SourceClaims, fn: string, text: string, from: string) => {
    const at = source.indexOf(text, source.indexOf(from));
    return { at, claim: must(claims.functions.find((f) => f.name === fn)?.expressions
      .find((e) => e.pos[0] === at && e.pos[1] === at + text.length), `${fn}'s ${text}`) };
  };
  const handler = readClaims(artifacts);
  const caught = claimAt(handler, "handlerParent", "n.parent", "return n.parent;");
  const absent = rowOf(handler, "undef");
  const honest = caught.claim.type;
  assert.ok(Array.isArray(honest) && honest.includes(absent), "the handler's parent may be absent");
  caught.claim.type = honest.filter((l) => l !== absent);
  const present = writeClaims(artifacts, "forged-guard-handler", handler);
  const span = `at [${caught.at},${caught.at + "n.parent".length})`;
  refusedAt(artifacts, present, "forged-guard-handler", span);
  assert.ok(invoke(present, join(artifacts, "evidence.json"), artifacts).includes(span));
  const widened = readClaims(artifacts);
  const operand = claimAt(widened, "parentNamed", "n.parent", "return ts.isIdentifier(n.parent) &&");
  const text = rowOf(widened, "str");
  const read = operand.claim.type;
  assert.ok(Array.isArray(read), "the argument's claim is a union");
  // A label list in canonical order: the document's rows first, by number.
  operand.claim.type = [...[...read.filter((l) => typeof l === "number"), text].sort((a, b) => a - b),
    ...read.filter((l) => typeof l !== "number")];
  const call = source.indexOf("ts.isIdentifier(n.parent) &&");
  const at = `at [${call},${call + "ts.isIdentifier(n.parent)".length})`;
  const outside = writeClaims(artifacts, "forged-guard-domain", widened);
  refusedAt(artifacts, outside, "forged-guard-domain", at);
  assert.ok(invoke(outside, join(artifacts, "evidence.json"), artifacts).includes(at));
  // `null` beside the argument's node or `undefined`: the audit is of
  // `undefined` alone, so the domain obligation refuses it.
  const nullable = readClaims(artifacts);
  const nulled = claimAt(nullable, "parentNamed", "n.parent", "return ts.isIdentifier(n.parent) &&");
  const nul = rowOf(nullable, "nul");
  const before = nulled.claim.type;
  assert.ok(Array.isArray(before), "the argument's claim is a union");
  nulled.claim.type = [...[...before.filter((l) => typeof l === "number"), nul].sort((a, b) => a - b),
    ...before.filter((l) => typeof l !== "number")];
  const withNull = writeClaims(artifacts, "forged-guard-null", nullable);
  refusedAt(artifacts, withNull, "forged-guard-null", at);
  assert.ok(invoke(withNull, join(artifacts, "evidence.json"), artifacts).includes(at));
  // The parser's document forged: every guard call's behaviour on
  // `undefined` stated `unadmitted`, refused at the domain obligation of a
  // call whose argument may be `undefined`; and left out, refused by the
  // document's decoder.
  const forgeCalls = (name: string, change: (call: object) => void): { searched: string; checked: string } => {
    const fragment: unknown = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
    const walk = (v: unknown): void => {
      if (Array.isArray(v)) v.forEach(walk);
      else if (typeof v === "object" && v !== null) {
        if ("k" in v && v.k === "tagMember") change(v);
        Object.values(v).forEach(walk);
      }
    };
    walk(fragment);
    const path = join(artifacts, `${name}.json`);
    const text = JSON.stringify(fragment);
    assert.ok(text !== undefined, "the document is JSON");
    writeFileSync(path, text);
    const searched = produceWith(artifacts, join(artifacts, "claims.json"), name, path);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    const checked = invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, path);
    return { searched: searched.stdout + searched.stderr, checked };
  };
  const unadmitted = forgeCalls("forged-guard-unadmitted", (c) => Reflect.set(c, "onUndefined", "unadmitted"));
  const searchedAt = /closure expression claim at \[(\d+),(\d+)\): evidence search failed/.exec(unadmitted.searched);
  assert.match(source.slice(Number(searchedAt?.[1]), Number(searchedAt?.[2])), /^ts\.is\w+\(\w+\.parent\)$/,
    "the search refuses a guard's call on a parent");
  // The honest evidence names the type of the error the dispatch throws,
  // which the forged document's lowering never states: the checker refuses
  // the evidence against it.
  assert.match(unadmitted.checked, /application of unknown head/);
  const unstated = forgeCalls("forged-guard-unstated", (c) => Reflect.deleteProperty(c, "onUndefined"));
  assert.match(unstated.searched, /onUndefined/);
  assert.match(unstated.checked, /onUndefined/);
  process.stdout.write("guards on undefined, forged claims: parent present in the throw's handler, refused at its read, and a string or null beside the guard's argument, refused at the call by the domain obligation, by the search and the checker; the document's behaviour on undefined stated unadmitted, refused at a call's domain obligation, and left out, refused by its decoder; the honest evidence refused against either\n");
});
control(async (): Promise<void> => {
  // Each correction of the compiler API's family (COMPILER-API.md,
  // "Corrections"), bypassing the producer: its negative fixture returns the
  // corrected member at its declared type. Read without that correction it
  // verifies; the claims and evidence of that run, offered with the
  // document the real description gives, which names the same definitions
  // in order, are refused by the search and by the checker at the read.
  const project = tsconfigOf(join(import.meta.dirname, "compiler-api-project"));
  const located = (detail: string, position: number): boolean =>
    [...detail.matchAll(/at \[(\d+),(\d+)\)/g)].some((m) => Number(m[1]) <= position && position < Number(m[2]));
  const fixtures = new Map([
    ["Node.parent", "source-file-parent"], ["PropertySignatureDeclaration.initializer", "property-signature-initializer"],
    ["PropertyAssignment.type", "property-assignment-type"], ["ShorthandPropertyAssignment.type", "shorthand-assignment-type"],
    ["ExportAssignment.type", "export-assignment-type"], ["DefaultClause.expression", "default-clause-expression"],
    ["TemplateLiteralLikeNodeBase.rawText", "template-raw-text"], ["TemplateLiteralLikeNodeBase.templateFlags", "template-flags"],
    ["TaggedTemplateExpression.questionDotToken", "tagged-template-question-dot"], ["JSDocTemplateTag.constraint", "template-tag-constraint"],
  ]);
  assert.equal(fixtures.size, compilerApiFamily.corrections.length, "a fixture for each correction");
  for (const correction of compilerApiFamily.corrections) {
    const slug = must(fixtures.get(`${correction.owner}.${correction.member}`), `the fixture of ${correction.owner}.${correction.member}`);
    const file = join(import.meta.dirname, "examples", `invalid-compiler-api-corrected-${slug}.ts`);
    const text = readFileSync(file, "utf8");
    const at = text.indexOf("return ") + "return ".length;
    useFamiliesForTests([{ ...compilerApiFamily, corrections: compilerApiFamily.corrections.filter((c) => c !== correction) }]);
    let plain: Outcome;
    try {
      plain = check(file, project);
    } finally {
      useFamiliesForTests(null);
    }
    assert.equal(plain.status, "verified", `${slug} uncorrected: ${JSON.stringify(plain)}`);
    const corrected = check(file, project);
    assert.ok(corrected.status === "unverified" && located(corrected.detail, at), `${slug}: ${JSON.stringify(corrected)}`);
    const identities = (dir: string): string[] => must(readFragmentFile(join(dir, "fragment.json")).declarations, "the declarations")
      .definitions.map((d) => JSON.stringify(d.declaration));
    assert.deepEqual(identities(corrected.artifacts), identities(plain.artifacts), `${slug}: one numbering`);
    const fragment = readFragmentFile(join(corrected.artifacts, "fragment.json"));
    const claims: unknown = JSON.parse(readFileSync(join(plain.artifacts, "claims.json"), "utf8"));
    assert.ok(typeof claims === "object" && claims !== null);
    const forged = join(corrected.artifacts, "forged-uncorrected.json");
    writeFileSync(forged, JSON.stringify({ ...claims, file: fragment.file }));
    const searched = produceWith(corrected.artifacts, forged, "forged-uncorrected");
    assert.ok(searched.status === 1 && located(searched.stdout + searched.stderr, at),
      `${slug}: the search refuses at the read: ${searched.stdout + searched.stderr}`);
    const checked = tested(verifierCall(verifier, ["--check-source-claims", join(corrected.artifacts, "fragment.json"), forged,
      sourceKey(corrected.artifacts), join(plain.artifacts, "evidence.json")]), 60_000);
    // The checker names the read, or refuses the evidence as a whole where
    // the corrected document's rows leave it justifying no claim.
    assert.ok(checked.status === 1 && (located(checked.stdout + checked.stderr, at) ||
      /evidence does not justify the extracted program and exact claims/.test(checked.stdout + checked.stderr)),
      `${slug}: the checker refuses: ${checked.stdout + checked.stderr}`);
  }
  process.stdout.write(`corrections: each of the ${compilerApiFamily.corrections.length} verifies uncorrected, and its claims and evidence are refused with the corrected document by the search at the read and by the checker\n`);
});
control(async (): Promise<void> => {
  // One tag selection per run (HOST-FAMILIES.md, "Residuals"): the importer
  // and the module it imports a function from name different kinds, and the
  // run reads every family declaration alike in both modules' documents,
  // the union of the kinds both name. The module's own run selects only its
  // own kinds.
  const artifacts = run("compiler-api-units");
  const ast: Ast = readFragmentFile(join(artifacts, "fragment.json"));
  const [module] = ast.modules;
  const family = (definitions: readonly TypeDefinition[]): Map<string, TypeDefinition> => new Map(definitions
    .filter((d) => d.declaration.module.startsWith("tscert/family/") || d.declaration.module.includes("/typescript/dist/ast/"))
    .map((d) => [`${d.declaration.module}#${d.declaration.name}`, d]));
  const main = family(must(ast.declarations, "the importer's declarations").definitions);
  const imported = family(must(must(module, "the imported module").declarations, "its declarations").definitions);
  assert.deepEqual([...imported.keys()].sort(), [...main.keys()].sort(), "both documents read the same family declarations");
  for (const [key, definition] of main)
    assert.equal(JSON.stringify(imported.get(key)), JSON.stringify(definition), `${key} is read alike in both modules`);
  const arms = (definitions: Map<string, TypeDefinition>): number[] => {
    const node = [...definitions].find(([key]) => key.endsWith("/ast.d.ts#Node"));
    const expression = must(node, "Node's reading")[1].expression;
    assert.ok(expression?.k === "union", "Node's reading is a union");
    return expression.parts.map((part) => part.k !== "reference" ? -2
      : part.reference.name === "NumericLiteral" ? 9 : part.reference.name === "Identifier" ? 80 : -1);
  };
  assert.deepEqual(arms(main), [9, 80, -1], "the run's Node: NumericLiteral, Identifier and a residual");
  const alone = check(join(import.meta.dirname, "compiler-api-project", "node-names.ts"),
    tsconfigOf(join(import.meta.dirname, "compiler-api-project")));
  assert.equal(alone.status, "verified", JSON.stringify(alone));
  const own: Ast = readFragmentFile(join(alone.artifacts, "fragment.json"));
  assert.deepEqual(arms(family(must(own.declarations, "the module's declarations").definitions)), [80, -1],
    "the module's own run: Identifier and a residual");
  process.stdout.write("tag selection: one per run, the importer's and its module's family readings equal; the module's own run selects its own kinds\n");
});
control(async (): Promise<void> => {
  // The wire orders a string set by Unicode code point, in every decoder:
  // U+E000 before U+10000, which UTF-16 code units would order first. The
  // producer's set is accepted by Lean and by the TypeScript decoder, and the
  // reverse is refused by both.
  const artifacts = run("tag-set-code-points");
  const original = readClaims(artifacts);
  const row = original.types.findIndex((r) => r.length === 1 && typeof r[0] === "object" && "strIn" in r[0] &&
    r[0].strIn.values.includes("\uE000") && r[0].strIn.values.includes("\u{10000}"));
  const clause = original.types[row]?.[0];
  assert.ok(typeof clause === "object" && "strIn" in clause, "the claims state the set of U+E000 and U+10000");
  const values = clause.strIn.values;
  assert.ok(values.indexOf("\uE000") < values.indexOf("\u{10000}"), "the producer orders by code point");
  decodeGraph([[clause]]);
  const reversed = { strIn: { values: [...values].reverse() } };
  assert.throws(() => decodeGraph([[reversed]]), /invalid string set/);
  const claims = readClaims(artifacts);
  claims.types[row] = [reversed];
  const forged = writeClaims(artifacts, "forged-code-point-order", claims);
  const searched = produceWith(artifacts, forged, "forged-code-point-order");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /a string set lists two or more strings, sorted and distinct/);
  process.stdout.write("string sets: ordered by code point in the producer, Lean and TypeScript\n");
});
control(async (): Promise<void> => {
  // Every wire string is well-formed Unicode (HOST-FAMILIES.md, "Tag sets"):
  // a lone surrogate, which JSON writes as an escape, and bytes that are not
  // UTF-8 are refused by every reader before it reads a value, in the
  // claims (Lean, TypeScript) and in the parser's document (the producer,
  // Lean).
  const artifacts = run("tag-set-code-points");
  const original = readClaims(artifacts);
  const row = original.types.findIndex((r) => r.length === 1 && typeof r[0] === "object" && "strIn" in r[0]);
  const lone = { strIn: { values: ["\ud800", ""] } };
  assert.throws(() => decodeGraph([[lone]]), /not well-formed Unicode/);
  const claims = readClaims(artifacts);
  claims.types[row] = [lone];
  const escaped = writeClaims(artifacts, "forged-lone-surrogate", claims);
  assert.ok(readFileSync(escaped, "utf8").includes("\\ud800"), "JSON writes the lone surrogate as an escape");
  const searched = produceWith(artifacts, escaped, "forged-lone-surrogate");
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /not well-formed Unicode, a lone high surrogate/);
  assert.throws(() => readClaimsFile(escaped), /not well-formed Unicode/);
  // Bytes that are no UTF-8, in place of a string's code point.
  const withByte = (text: string): Buffer => {
    const bytes = Buffer.from(text.replace("", "\u0001"), "utf8");
    const at = bytes.indexOf(0x01);
    assert.ok(at >= 0, "the document holds U+E000");
    bytes[at] = 0xff;
    return bytes;
  };
  const raw = join(artifacts, "forged-invalid-utf8.json");
  writeFileSync(raw, withByte(readFileSync(join(artifacts, "claims.json"), "utf8")));
  assert.throws(() => readClaimsFile(raw), /not valid UTF-8/);
  const rawSearched = produceWith(artifacts, raw, "forged-invalid-utf8");
  assert.equal(rawSearched.status, 1, rawSearched.stdout + rawSearched.stderr);
  assert.match(rawSearched.stdout + rawSearched.stderr, /^reject: .*a text that is not valid UTF-8 is refused/);
  // The parser's document, read by the producer and by Lean.
  const fragment = readFileSync(join(artifacts, "fragment.json"), "utf8");
  assert.ok(fragment.includes(""), "the fragment holds U+E000");
  const flow = join(artifacts, "flow.json");
  const loneFragment = join(artifacts, "forged-lone-surrogate-fragment.json");
  writeFileSync(loneFragment, fragment.replace("", "\\ud800"));
  const proposed = tested(producerCall(producerExecutable, [loneFragment, flow]));
  assert.notEqual(proposed.status, 0, proposed.stdout + proposed.stderr);
  assert.match(proposed.stdout + proposed.stderr, /low surrogate/);
  assert.throws(() => readFragmentFile(loneFragment), /not well-formed Unicode/);
  const leanFragment = produceWith(artifacts, join(artifacts, "claims.json"), "forged-lone-fragment", loneFragment);
  assert.equal(leanFragment.status, 1, leanFragment.stdout + leanFragment.stderr);
  assert.match(leanFragment.stdout + leanFragment.stderr, /not well-formed Unicode/);
  const rawFragment = join(artifacts, "forged-invalid-utf8-fragment.json");
  writeFileSync(rawFragment, withByte(fragment));
  const rawProposed = tested(producerCall(producerExecutable, [rawFragment, flow]));
  assert.notEqual(rawProposed.status, 0, rawProposed.stdout + rawProposed.stderr);
  assert.match(rawProposed.stdout + rawProposed.stderr, /not valid UTF-8/);
  process.stdout.write("wire strings: lone surrogates and invalid UTF-8 refused by the producer, Lean and TypeScript\n");
});
control(async (): Promise<void> => {
  // A node states its sequent once (REQUEST-PROTOCOL.md, "Evidence"): by its
  // ordinary derivation, by the proof its step carries, or by itself. Every
  // consumer reads a node as the one with its derivation written out, so a
  // referenced proof written out, a proof-less step's sequent stated alone
  // and an ordinary derivation without step evidence are accepted beside the
  // honest document. A second statement of the sequent, a reference no step
  // supplies, a node stating its sequent nowhere (a sliced read's proof, at
  // the location's contract, supplies none), and a node without step
  // evidence or derivation are refused by the decoder; a step proof at
  // another sequent than the node's derivation by the step check.
  type Evidence = { main: { functions: { certificate: WireNode[] }[] } };
  const nodes = (e: Evidence): WireNode[] => e.main.functions.flatMap((f) => f.certificate);
  const proofOf = (n: WireNode): WireDerivation | undefined =>
    Object.values(must(n.effect, "the producer gives every node step evidence"))[0]?.proof;
  const stepOf = (n: WireNode): string => must(Object.keys(must(n.effect, "step evidence"))[0], "a step");
  const referencing = (n: WireNode): boolean => n.ordinary === "effect";
  const proofFree = (n: WireNode): boolean => n.ordinary !== "effect" && proofOf(n) === undefined;
  const spelling = /a node states its sequent once/;
  const forgery = (artifacts: string) => {
    const honest = (): Evidence =>
      unfoldedEvidence(join(artifacts, "evidence.json")) as Evidence; // asserted: the case's verifier-produced evidence; Lean decodes every forged document independently
    const forge = (name: string, change: (e: Evidence) => void): string => {
      const e = honest();
      change(e);
      const path = join(artifacts, `forged-node-${name}-evidence.json`);
      writeFileSync(path, tabledEvidence(e));
      return path;
    };
    const at = (pick: (n: WireNode) => boolean, change: (n: WireNode) => void) => (e: Evidence): void =>
      change(must(nodes(e).find(pick), "the forged node"));
    const check = (evidence: string): Invoked => tested(verifierCall(verifier, ["--check-source-claims",
      join(artifacts, "fragment.json"), join(artifacts, "claims.json"), sourceKey(artifacts), evidence]));
    return { honest, forge, at, check };
  };
  const aliases = run("aliases");
  const { honest, forge, at, check } = forgery(aliases);
  assert.ok(nodes(honest()).some(referencing), "a node referencing its step's proof");
  assert.ok(nodes(honest()).some(proofFree), "a node whose step carries no proof");
  for (const [name, change] of [
    ["written-out", at(referencing, (n) => { n.ordinary = { proof: { tree: must(proofOf(n), "the referenced proof") } }; })],
    ["stated-alone", at(proofFree, (n) => { n.sequent = nodeSequent(n); n.ordinary = null; })],
  ] as const) {
    const accepted = check(forge(name, change));
    assert.equal(accepted.status, 0, `${name}: ${accepted.stdout}${accepted.stderr}`);
  }
  for (const [name, change] of [
    ["twice", at(referencing, (n) => { n.sequent = nodeSequent(n); })],
    ["stated-beside-proof", at(referencing, (n) => { n.sequent = nodeSequent(n); n.ordinary = null; })],
    ["no-step-proof", at(proofFree, (n) => { n.ordinary = "effect"; })],
    ["stated-nowhere", at(proofFree, (n) => { n.ordinary = null; })],
    ["sliced-read-proof", at(proofFree, (n) => {
      const proof = n.ordinary !== null && n.ordinary !== "effect" ? n.ordinary.proof.tree : undefined;
      n.effect = { slicedRead: { tag: "isNul", answer: false, slot: 0, proof: must(proof, "the node's own derivation"),
        sub: { instantiation: null, members: [] } } };
      n.ordinary = null;
    })],
    ["no-step-no-derivation", at(referencing, (n) => { n.effect = null; n.ordinary = null; })],
  ] as const) assert.match(invoke(join(aliases, "claims.json"), forge(name, change), aliases), spelling, name);
  // A step proof at another node's sequent beside the node's own derivation
  // written out: a well-spelled node whose step check refuses the proof.
  const otherRoot = check(forge("other-root", (e) => {
    const all = nodes(e).filter(referencing);
    const n = must(all[0], "a referencing node");
    const proof = must(proofOf(n), "its proof");
    const other = must(all.map(proofOf).find((p) => p !== undefined &&
      JSON.stringify(p.node.claim) !== JSON.stringify(proof.node.claim)), "a proof at another sequent");
    n.ordinary = { proof: { tree: proof } };
    n.effect = { [stepOf(n)]: { proof: other } };
  }));
  assert.equal(otherRoot.status, 1, otherRoot.stdout + otherRoot.stderr);
  assert.match(otherRoot.stdout + otherRoot.stderr, /the evidence does not establish this node's typing/);
  // An ordinary derivation without step evidence: the step an ordinary
  // step's proof gives, written as the node's derivation, is that step.
  const methods = forgery(run("callables/methods"));
  const ordinaryStep = methods.check(methods.forge("no-step", methods.at(
    (n) => referencing(n) && n.effect !== null && "ordinary" in n.effect,
    (n) => { n.ordinary = { proof: { tree: must(proofOf(n), "the ordinary step's proof") } }; n.effect = null; })));
  assert.equal(ordinaryStep.status, 0, ordinaryStep.stdout + ordinaryStep.stderr);
  process.stdout.write("node headers: a referenced proof written out, a proof-less step's sequent stated alone and an ordinary derivation without step accepted; a sequent stated twice or nowhere, a reference without a step proof, a sliced read's proof as the header and a node without step or derivation refused by the decoder; a step proof at another sequent by the step check\n");
});
control(async (): Promise<void> => {
  // The evidence document's references (REQUEST-PROTOCOL.md, "Evidence
  // document"): a reference past its table, an entry of another kind, a
  // derivation naming itself or a later one as a premise are refused by
  // the decoder; a reference to another entry of the right kind, whose
  // value is not the one the node's claim needs, by the check. An entry
  // stated twice and used once each, and an entry no reference uses, are
  // accepted: they denote the same bundle.
  const artifacts = run("aliases");
  const check = (name: string, change: (b: JsonObject) => void): Invoked => {
    const document = jsonValue(JSON.parse(readFileSync(join(artifacts, "evidence.json"), "utf8")));
    change(evidenceBundles(document)[0] ?? {});
    const path = join(artifacts, `forged-reference-${name}-evidence.json`);
    writeFileSync(path, jsonText(document));
    return tested(verifierCall(verifier, ["--check-source-claims", join(artifacts, "fragment.json"),
      join(artifacts, "claims.json"), sourceKey(artifacts), path]));
  };
  const nodes = (b: JsonObject): JsonObject[] =>
    jsonArray(b.functions).flatMap((f) => jsonArray(jsonObject(f).certificate).map(jsonObject));
  const proofs = (b: JsonObject): JsonObject[] => jsonArray(b.proofs).map(jsonObject);
  /** The first derivation with premises, and its position. */
  const withPremises = (b: JsonObject): [JsonObject, number] => {
    const k = proofs(b).findIndex((p) => jsonArray(p.premises).length > 0);
    assert.ok(k >= 0, "a derivation with premises");
    return [must(proofs(b)[k], "the derivation"), k];
  };
  /** A node whose ordinary derivation is a separate tree, and that tree's position. */
  const separate = (b: JsonObject): [JsonObject, number] => {
    const n = must(nodes(b).find((m) => typeof m.ordinary === "object" && m.ordinary !== null &&
      !Array.isArray(m.ordinary)), "a node with its own derivation");
    return [n, jsonIndex(jsonObject(jsonObject(n.ordinary).proof).tree)];
  };
  const refused: [string, (b: JsonObject) => void, RegExp][] = [
    ["knowledge-past-table", (b) => { must(nodes(b)[0], "a node").knowledge = jsonArray(b.knowledge).length; },
      /a reference to knowledge \d+, not among the knowledge entries it may name/],
    ["type-past-table", (b) => { jsonArray(b.contexts)[0] = [jsonArray(b.types).length]; },
      /a reference to type \d+, not among the type entries it may name/],
    ["proof-as-knowledge", (b) => { jsonArray(b.proofs)[0] = must(jsonArray(b.knowledge)[0], "a knowledge entry"); },
      /Document\.proofs: Verification\.EvidenceWire\.ProofEntry\./],
    ["separation-past-table", (b) => {
      must(jsonObject(jsonArray(b.knowledge)[0]), "a knowledge entry").separation = [jsonArray(b.separations).length];
    }, /a reference to separation fact \d+, not among the separation fact entries it may name/],
    ["knowledge-as-link", (b) => { jsonArray(b.links)[0] = must(jsonArray(b.knowledge)[0], "a knowledge entry"); },
      /Document\.links: Verification\.HeapLinks\.Link\./],
    ["premise-itself", (b) => { const [p, k] = withPremises(b); jsonArray(p.premises)[0] = k; },
      /a reference to proof \d+, not among the proof entries it may name/],
    ["premise-later", (b) => { const [p] = withPremises(b); jsonArray(p.premises)[0] = jsonArray(b.proofs).length - 1; },
      /a reference to proof \d+, not among the proof entries it may name/],
  ];
  for (const [name, change, refusal] of refused) {
    const checked = check(name, change);
    assert.equal(checked.status, 1, `${name}: ${checked.stdout}${checked.stderr}`);
    assert.match(checked.stdout + checked.stderr, refusal, name);
  }
  // A node's derivation, a premise and a sequent's context, each moved to
  // another entry of its table, are read and refused by the check.
  const differing: [string, (b: JsonObject) => void][] = [
    ["other-derivation", (b) => {
      const [n, k] = separate(b);
      const claim = JSON.stringify(must(proofs(b)[k], "its derivation").claim);
      const other = proofs(b).findIndex((p) => JSON.stringify(p.claim) !== claim);
      assert.ok(other >= 0, "a derivation at another sequent");
      jsonObject(jsonObject(n.ordinary).proof).tree = other;
    }],
    ["other-premise", (b) => {
      const k = proofs(b).reduce((last, q, i) => jsonArray(q.premises).length > 0 ? i : last, -1);
      const p = must(proofs(b)[k], "the last derivation with premises");
      const first = jsonIndex(jsonArray(p.premises)[0]);
      const claim = JSON.stringify(must(proofs(b)[first], "the premise").claim);
      const other = proofs(b).findIndex((q, i) => i < k && JSON.stringify(q.claim) !== claim);
      assert.ok(other >= 0, "an earlier derivation at another sequent");
      jsonArray(p.premises)[0] = other;
    }],
    ["other-context", (b) => {
      const [, k] = separate(b);
      const claim = jsonObject(must(proofs(b)[k], "its derivation").claim);
      const contexts = jsonArray(b.contexts);
      const other = contexts.findIndex((c, i) => i !== jsonIndex(claim.context) &&
        JSON.stringify(c) !== JSON.stringify(contexts[jsonIndex(claim.context)]));
      assert.ok(other >= 0, "another context");
      claim.context = other;
    }],
  ];
  for (const [name, change] of differing) {
    const checked = check(name, change);
    assert.equal(checked.status, 1, `${name}: ${checked.stdout}${checked.stderr}`);
    assert.match(checked.stdout + checked.stderr, /^reject: source (evidence|incoming edge obligation|expression obligation)/m, name);
    assert.doesNotMatch(checked.stdout + checked.stderr, /entries it may name|Verification\.EvidenceWire\.Document\./, name);
  }
  const accepted: [string, (b: JsonObject) => void][] = [
    ["stated-twice", (b) => {
      const [n, k] = separate(b);
      jsonArray(b.proofs).push(must(proofs(b)[k], "its derivation"));
      jsonObject(jsonObject(n.ordinary).proof).tree = jsonArray(b.proofs).length - 1;
    }],
    ["unused", (b) => { jsonArray(b.knowledge).push({ cells: [], values: [], links: [], depth: 0, separation: [] }); }],
  ];
  for (const [name, change] of accepted) {
    const checked = check(name, change);
    assert.equal(checked.status, 0, `${name}: ${checked.stdout}${checked.stderr}`);
  }
  process.stdout.write("evidence references: a reference past its table, an entry of another kind and a premise at or after its derivation refused by the decoder; a derivation, a premise and a context moved to another entry refused by the check; an entry stated twice and an unused entry accepted\n");
});
control(async (): Promise<void> => {
  // A request's read summaries (REQUEST-PROTOCOL.md, "Read summaries") are
  // checked once each, used or not, against the request's graph and image
  // check: an entry whose arms miss or add a member, compare a view to a
  // result it is not within, or read a key no member states as a readonly
  // view (a `length` view at a number, a writable field, an optional field,
  // a dictionary's index, a key every object reads through its prototype,
  // the field of a receiver coerced to its base, a class value's static
  // field or a constructor's readonly field, each stated with the arms the
  // honest per-member derivation states, a captured cell's value) is
  // refused by the table check, beside an accepted entry differing in that
  // part (a copy, a `length` view at a type excluding a number, an entry at
  // a wider result); an entry stating a location's contents or a heap link
  // by the decoder; a valid entry at another receiver, key or result than
  // the read's, an index past the table and an entry of another request's
  // table by the use check. The same holds in a body qualified by its
  // binder's resolution descriptor (`Awaited<T>`), which reads through an
  // ordinary summary in a typed read, an inspection and, written so, an
  // ordinary step, checked with the body's rule, and in a closure's code, checked before the unit's
  // graph against the codes before it. A typed read is checked against the
  // unit's code table where every member states the key as a field or view
  // (kindOf's at A | B), and against no code entry otherwise (entryKind's at
  // D | A, a dictionary among its members, read in the step's optional
  // branch): a summary names no code, so both accept it and both refuse a
  // use past the table. The reads outside the boundary keep their rules in
  // the honest evidence.
  type Arm = { view: number[]; proof: unknown };
  type Summary = { receiver: number[]; field: string; result: number[]; arms: Arm[] };
  type Unit = { certificate: WireNode[]; codes?: WireNode[][]; readSummaries?: Summary[] };
  type Evidence = { main: { functions: Unit[] } };
  type Claim = { context: unknown[]; term: unknown; type: number[] };
  const artifacts = run("read-summaries");
  const names = readClaimsFile(join(artifacts, "claims.json")).functions.map((f) => f.name);
  const at = (name: string): number => {
    const i = names.indexOf(name);
    assert.ok(i >= 0, `the unit ${name}`);
    return i;
  };
  const honest = (): Evidence =>
    unfoldedEvidence(join(artifacts, "evidence.json")) as Evidence; // asserted: the case's verifier-produced evidence; Lean decodes every forged document independently
  const unit = (e: Evidence, name: string): Unit => must(e.main.functions[at(name)], name);
  const table = (e: Evidence, name: string): Summary[] => must(unit(e, name).readSummaries, `${name}'s summaries`);
  /** Every value nested in `value`, depth first. */
  const nested = (value: unknown): unknown[] => [value, ...(Array.isArray(value) ? value.flatMap(nested)
    : typeof value === "object" && value !== null ? Object.values(value).flatMap(nested) : [])];
  const claims = (value: unknown): Claim[] => nested(value).flatMap((v) =>
    typeof v === "object" && v !== null && "claim" in v ? [v.claim as Claim] : []); // asserted: a derivation node's claim, as the wire spells it
  const uses = (value: unknown): { index: number }[] => nested(value).flatMap((v) =>
    typeof v === "object" && v !== null && "readSummary" in v ? [v.readSummary as { index: number }] : []); // asserted: a derivation node's rule, as the wire spells it
  /** The rules a unit's derivations apply, by name. */
  const rules = (value: unknown): Set<string> => new Set(nested(value).flatMap((v) =>
    typeof v !== "object" || v === null || !("rule" in v) ? [] : typeof v.rule === "string" ? [v.rule]
      : typeof v.rule === "object" && v.rule !== null ? Object.keys(v.rule) : []));
  const readOf = (u: unknown, field: string): Claim => must(claims(u).find((c) =>
    (JSON.stringify(c.term) ?? "").includes(`"field":"${field}"`) && (JSON.stringify(c.term) ?? "").startsWith('{"readAt"')),
    `a read of ${field}`);
  const e0 = honest();
  const S = must(table(e0, "kindOf")[0], "kindOf's summary");
  assert.equal(S.field, "k");
  assert.equal(S.arms.length, 2, "one arm per member of A | B");
  assert.equal(uses(unit(e0, "kindTwice")).length, 2, "two reads of one summary in kindTwice");
  assert.equal(table(e0, "kindTwice").length, 1, "one summary for both reads");
  for (const name of ["kindOf", "tagOf", "entryKind", "lengthView", "kindAwaiting", "numberedKindAwaiting"])
    assert.equal(uses(unit(e0, name)).length, 1, `${name} reads through a summary`);
  assert.ok(uses(unit(e0, "kindOfCell").codes).length > 0, "the closure's code reads through a summary");
  /** The steps of a unit's nodes whose proof reads through a summary. */
  const summarizedSteps = (u: Unit): string[] => u.certificate.flatMap((n) =>
    n.effect !== null && uses(n.effect).length > 0 ? Object.keys(n.effect) : []);
  for (const name of ["kindOf", "entryKind"])
    assert.deepEqual(summarizedSteps(unit(e0, name)), ["typedRead"], `${name}'s read is a typed read through a summary`);
  // At N | A, N a dictionary with a numeric index only, the read is an
  // inspection (`reading`); written as an ordinary step, the qualified
  // body's checker checks it with the body's subsumption rule.
  assert.deepEqual(summarizedSteps(unit(e0, "numberedKindAwaiting")), ["reading"], "an inspection through a summary");
  const ordinaryStep = (name: string) => (e: Evidence): void => {
    for (const n of unit(e, name).certificate)
      if (n.effect !== null && "reading" in n.effect && uses(n.effect).length > 0) n.effect = { ordinary: must(n.effect.reading, "the inspection") };
  };
  for (const [name, rule] of [["widthOf", "read"], ["optionalOf", "readOptional"], ["indexOf", "readDict"],
      ["tagOfCallable", "readCallable"], ["classTag", "readCallable"], ["constructorTag", "readBagView"], ["errorName", "read"], ["sizeOf", "len"], ["textSize", "lenStr"],
      ["upper", "readProto"]] as const) {
    assert.equal(uses(unit(e0, name)).length, 0, `${name} reads through no summary`);
    assert.ok(rules(unit(e0, name)).has(rule), `${name} reads by ${rule}`);
  }
  const [armA, armB] = [must(S.arms[0], "A's arm"), must(S.arms[1], "B's arm")];
  const tagged = must(table(e0, "tagOf")[0], "tagOf's summary");
  const lengths = must(table(e0, "lengthView")[0], "lengthView's summary");
  assert.equal(lengths.field, "length");
  const num = readOf(unit(e0, "widthOf"), "w").type;
  const str = readOf(unit(e0, "errorName"), "name").type;
  const dictionary = must(must(table(e0, "entryKind")[0], "entryKind's summary").receiver.find((l) => !S.receiver.includes(l)), "D");
  const errors = must(readOf(unit(e0, "errorName"), "name").context[0], "the error slot's type") as number[]; // asserted: a context entry is a type
  const statics = readOf(unit(e0, "classTag"), "tag");
  const classes = must(statics.context[0], "the class slot's type") as number[]; // asserted: a context entry is a type
  type Derivation = { node: { claim: Claim; rule: unknown; premises: Derivation[] } };
  /** The arms a per-member split states: each member's own read type, and
   * the comparison its arm makes to the split's result. */
  const armsOf = (u: Unit, field: string): Arm[] => {
    const derivations = nested(u).filter((v) => typeof v === "object" && v !== null && "node" in v)
      .map((v) => v as Derivation); // asserted: a derivation node, as the wire spells it
    const split = must(derivations.find((d) => (JSON.stringify(d.node.rule) ?? "").startsWith('{"unionVar"') &&
      (JSON.stringify(d.node.claim.term) ?? "").includes(`"field":"${field}"`)), `a split read of ${field}`);
    return split.node.premises.map((p) => {
      const rule = p.node.rule;
      return typeof rule === "object" && rule !== null && "sub" in rule
        ? { view: must(p.node.premises[0], "the arm's read").node.claim.type, proof: (rule.sub as { proof: unknown }).proof } // asserted: a `sub` rule's fields, as the wire spells them
        : { view: p.node.claim.type, proof: null };
    });
  };
  const views = readOf(unit(e0, "constructorTag"), "tag");
  const constructors = must(views.context[0], "the constructor slot's type") as number[]; // asserted: a context entry is a type
  const cellRead = readOf(unit(e0, "kindOfCell").codes, "value");
  const cellUse = must(nested(cellRead.term).find((v) => typeof v === "object" && v !== null && "var" in v), "the cell's slot") as { var: { i: number } }; // asserted: the read's receiver term
  const cell = must(cellRead.context[cellUse.var.i], "the cell's type") as number[]; // asserted: a context entry is a type
  const forge = (name: string, change: (e: Evidence) => void): string => {
    const e = honest();
    change(e);
    const path = join(artifacts, `forged-summary-${name}-evidence.json`);
    writeFileSync(path, tabledEvidence(e));
    return path;
  };
  const check = (path: string): Invoked => tested(verifierCall(verifier, ["--check-source-claims",
    join(artifacts, "fragment.json"), join(artifacts, "claims.json"), sourceKey(artifacts), path]));
  const added = (entry: Summary, use: boolean = false, name: string = "kindOf") => (e: Evidence): void => {
    const t = table(e, name);
    t.push(entry);
    if (use) for (const u of uses(unit(e, name))) u.index = t.length - 1;
  };
  const wider: Summary = { ...structuredClone(S), result: [...armA.view, ...armB.view] };
  const accepted: [string, (e: Evidence) => void][] = [
    ["copy-used", added(structuredClone(S), true)],
    ["copy-unused", added(structuredClone(S))],
    ["narrower-unused", added({ receiver: [must(S.receiver[0], "A")], field: "k", result: S.result, arms: [armA] })],
    ["wider-result-unused", added(structuredClone(wider))],
    ["other-key-unused", added(structuredClone(tagged))],
    ["length-view-unused", added(structuredClone(lengths))],
    ["qualified-copy-used", added(structuredClone(S), true, "kindAwaiting")],
    ["qualified-ordinary-step", ordinaryStep("numberedKindAwaiting")],
    ["restricted-copy-used", (e) => added(structuredClone(must(table(e0, "entryKind")[0], "entryKind's summary")), true,
      "entryKind")(e)],
  ];
  for (const [name, change] of accepted) {
    const outcome = check(forge(name, change));
    assert.equal(outcome.status, 0, `${name}: ${outcome.stdout}${outcome.stderr}`);
  }
  const typing = /does not establish this node's typing/;
  const refused: [string, (e: Evidence) => void, RegExp][] = [
    ["missing-arm", (e) => { must(table(e, "kindOf")[0], "S").arms.pop(); }, /does not justify/],
    ["extra-arm", (e) => { must(table(e, "kindOf")[0], "S").arms.push(armA); }, /does not justify/],
    ["arm-not-within", added({ ...structuredClone(S), result: armA.view, arms: [{ view: armA.view, proof: null }, armB] }), /does not justify/],
    ["length-view", added({ receiver: S.receiver, field: "length", result: num, arms: [{ view: num, proof: null }, { view: num, proof: null }] }), /does not justify/],
    ["writable-field", added({ receiver: S.receiver, field: "w", result: num, arms: [{ view: num, proof: null }, { view: num, proof: null }] }), /does not justify/],
    ["optional-field", added({ receiver: S.receiver, field: "o", result: num, arms: [{ view: num, proof: null }, { view: num, proof: null }] }), /does not justify/],
    ["index", added({ receiver: [dictionary], field: "other", result: str, arms: [{ view: str, proof: null }] }), /does not justify/],
    ["prototype-key", added({ receiver: S.receiver, field: "toString", result: str, arms: [{ view: str, proof: null }, { view: str, proof: null }] }), /does not justify/],
    ["coerced-receiver", added({ receiver: errors, field: "name", result: str, arms: errors.map(() => ({ view: str, proof: null })) }), /does not justify/],
    ["class-static", added({ receiver: classes, field: "tag", result: statics.type, arms: armsOf(unit(e0, "classTag"), "tag") }),
      /does not justify/],
    ["constructor-view", added({ receiver: constructors, field: "tag", result: views.type,
      arms: armsOf(unit(e0, "constructorTag"), "tag") }), /does not justify/],
    ["cell-contents", added({ receiver: cell, field: "value", result: S.receiver, arms: [{ view: S.receiver, proof: null }] }), /does not justify/],
    ["other-receiver", added({ receiver: [must(S.receiver[0], "A")], field: "k", result: S.result, arms: [armA] }, true), typing],
    ["other-result", added(structuredClone(wider), true), typing],
    ["other-key", added(structuredClone(tagged), true), typing],
    ["past-the-table", (e) => { for (const u of uses(unit(e, "kindOf"))) u.index = 9; }, typing],
    ["other-request", (e) => { delete unit(e, "kindOf").readSummaries; }, typing],
    ["qualified-missing-arm", (e) => { must(table(e, "kindAwaiting")[0], "its summary").arms.pop(); }, /does not justify/],
    ["qualified-other-result", added(structuredClone(wider), true, "kindAwaiting"), typing],
    ["qualified-ordinary-past-the-table", (e) => {
      ordinaryStep("numberedKindAwaiting")(e);
      for (const u of uses(unit(e, "numberedKindAwaiting"))) u.index = 9;
    }, typing],
    ["qualified-ordinary-other-result", (e) => {
      ordinaryStep("numberedKindAwaiting")(e);
      const own = must(table(e0, "numberedKindAwaiting")[0], "its summary");
      added({ ...structuredClone(own), result: own.arms.flatMap((a) => a.view) }, true, "numberedKindAwaiting")(e);
    }, typing],
    ["code-past-the-table", (e) => { for (const u of uses(unit(e, "kindOfCell").codes)) u.index = 9; }, /does not justify|does not establish/],
    ["restricted-past-the-table", (e) => { for (const u of uses(unit(e, "entryKind"))) u.index = 9; }, typing],
    ["cached-contents", (e) => { Object.assign(must(table(e, "kindOf")[0], "S"), { contents: ["str"] }); },
      /unknown fields or missing explicit fields/],
    ["heap-link", (e) => { Object.assign(must(table(e, "kindOf")[0], "S"), { links: [] }); },
      /unknown fields or missing explicit fields/],
  ];
  for (const [name, change, reason] of refused) {
    const outcome = check(forge(name, change));
    assert.equal(outcome.status, 1, `${name}: ${outcome.stdout}${outcome.stderr}`);
    assert.match(outcome.stdout + outcome.stderr, reason, name);
  }
  process.stdout.write(`read summaries: 8 units read through summaries (two qualified bodies', a closure's code's and a typed read's against no code entry among them) and 10 read outside the boundary by their own rules in the honest evidence; ${accepted.length} copies and valid entries accepted; ${refused.length} forged entries and uses refused (a missing or extra arm, a view not within the result, a length view at a number, a writable, optional, index, prototype, coerced-receiver, class-static, constructor-view or cell key by the table check; contents or a link by the decoder; another receiver, key or result, an index past the table and another request's entry by the use check; likewise in a qualified body's typed read and ordinary step, the closure's code and the typed read checked against no code entry)\n`);
});
control(async (): Promise<void> => {
  // The evidence decoder reads the parsed JSON value (REQUEST-PROTOCOL.md,
  // "Wire text"): spellings the JSON parser reads as the same value are the
  // same document, whatever their key order, whitespace or escapes, and a
  // repeated key holds its last value; a natural number is an integer
  // literal, its exponent form included, and a fraction is refused.
  const artifacts = run("aliases");
  const text = readFileSync(join(artifacts, "evidence.json"), "utf8");
  const slot = '"slot":0', field = '"field":"value"';
  const at = text.indexOf(slot), named = text.indexOf(field);
  assert.ok(at >= 0 && named >= 0, "a slot 0 and a field named value in the honest document");
  const replaced = (i: number, old: string, by: string): string => text.slice(0, i) + by + text.slice(i + old.length);
  const reversed = (value: unknown): unknown => Array.isArray(value) ? value.map(reversed)
    : typeof value === "object" && value !== null
      ? Object.fromEntries(Object.entries(value).reverse().map(([k, v]) => [k, reversed(v)])) : value;
  const parsed: unknown = JSON.parse(text);
  const variants: [string, string, boolean][] = [
    ["exponent", replaced(at, slot, '"slot":0e0'), true],
    ["negative-zero", replaced(at, slot, '"slot":-0'), true],
    ["fraction", replaced(at, slot, '"slot":0.0'), false],
    ["repeated-honest-last", replaced(at, slot, '"slot":7,"slot":0'), true],
    ["repeated-honest-first", replaced(at, slot, '"slot":0,"slot":7'), false],
    ["indented", must(JSON.stringify(parsed, null, 1), "the document's text"), true],
    ["reordered", must(JSON.stringify(reversed(parsed)), "the document's text"), true],
    ["escaped-key", replaced(named, field, '"fi\\u0065ld":"value"'), true],
  ];
  for (const [name, variant, accepted] of variants) {
    const path = join(artifacts, `spelled-${name}-evidence.json`);
    writeFileSync(path, variant);
    const checked = tested(verifierCall(verifier, ["--check-source-claims", join(artifacts, "fragment.json"),
      join(artifacts, "claims.json"), sourceKey(artifacts), path]));
    assert.equal(checked.status, accepted ? 0 : 1, `${name}: ${checked.stdout}${checked.stderr}`);
  }
  process.stdout.write("evidence spellings: key order, whitespace, key escapes, an exponent and a negative zero read as the parsed value, a repeated key as its last value; a fractional natural number refused\n");
});
control(async (): Promise<void> => {
  // A step's exit other than its complete refusal record (the verifier's
  // exit 1, a first line `reject: …` and a last line `end of refusal`; the
  // producer's exit 2 and `unsupported: …`) is a tool failure, no verdict:
  // no output, an exception's text, and a record cut short, at each step
  // whose refusal is a verdict; and an `--explain` run of the producer that
  // fails or prints no explanations.
  // The injected failure is written into each stand-in, so it is part of the
  // executable the invocation runs. A stand-in is no audited program, so its
  // invocations execute without a key while the other stages replay; each
  // run asserts that the failing stage ran.
  const dir = runDirectory("tscert-step-failures-");
  type Failure = { FAIL_MODE: string; FAIL_TEXT?: string; FAIL_STATUS?: string; FAIL_OUT?: string };
  const stageOfMode: Record<string, string> = { "--lower-control-flow": "lower", "--produce-source-claims": "search",
    "--check-source-claims": "check", "--explain": "explain" };
  const fake = (at: string, name: string, real: string, status: number, failure: Failure): string => {
    const path = join(at, name);
    const quoted = (s: string): string => `'${s.replaceAll("'", `'\\''`)}'`;
    writeFileSync(path, `#!/bin/sh\nFAIL_MODE=${quoted(failure.FAIL_MODE)}\nFAIL_TEXT=${quoted(failure.FAIL_TEXT ?? "")}\n` +
      `FAIL_OUT=${quoted(failure.FAIL_OUT ?? "")}\nFAIL_STATUS=${quoted(failure.FAIL_STATUS ?? "")}\n` +
      `if [ "$1" = "$FAIL_MODE" ]; then\n  [ -n "$FAIL_TEXT" ] && echo "$FAIL_TEXT" >&2\n` +
      `  [ -n "$FAIL_OUT" ] && echo "$FAIL_OUT"\n  exit \${FAIL_STATUS:-${status}}\nfi\nexec "${real}" "$@"\n`);
    chmodSync(path, 0o755);
    return path;
  };
  let runs = 0;
  const outcomeOf = (source: string, failure: Failure): Outcome => {
    const at = join(dir, `run-${runs++}`);
    mkdirSync(at);
    const ran = spawnSync(process.execPath, [join(here, "verify-source.mts"), join(here, "examples", source)],
      { encoding: "utf8", timeout: 120_000, env: { ...process.env,
        VERIFIER: fake(at, "verifier.sh", verifier, 1, failure),
        PRODUCER: fake(at, "producer.sh", producerExecutable, 2, failure) } });
    const outcome = readOutcome(JSON.parse(ran.stdout.slice(ran.stdout.indexOf("{"))));
    const failing = readInvocationLog(join(outcome.artifacts, invocationLog))
      .filter((r) => r.stage === stageOfMode[failure.FAIL_MODE]).at(-1);
    assert.ok(failing && ranStage(failing) && failing.key === null, `${failure.FAIL_MODE}: the failing stage ran, without a key`);
    return outcome;
  };
  for (const mode of ["--lower-control-flow", "--produce-source-claims", "--check-source-claims"])
    for (const text of ["", "uncaught exception: forced by pipeline/test.mts", "reject: a record cut short"]) {
      const outcome = outcomeOf("optional-chain-element-receiver.ts", { FAIL_MODE: mode, FAIL_TEXT: text });
      assert.equal(outcome.status, "error", `${mode} ${JSON.stringify(text)}: ${JSON.stringify(outcome)}`);
      assert.equal(outcome.detail,
        `tool failure: verifier ${mode} exited with status 1 without a complete refusal: ${text || "no output"}`);
    }
  // The producer's run is told by its arguments' count, the fragment first.
  const cut = outcomeOf("invalid-closure-contextual-result.ts", { FAIL_MODE: "--explain", FAIL_STATUS: "2" });
  assert.equal(cut.status, "error", JSON.stringify(cut));
  assert.equal(cut.detail, "tool failure: the producer's --explain exited with status 2: no output");
  const garbled = outcomeOf("invalid-closure-contextual-result.ts", { FAIL_MODE: "--explain", FAIL_STATUS: "0", FAIL_OUT: "[{\"pos\":1}]" });
  assert.equal(garbled.status, "error", JSON.stringify(garbled));
  assert.match(garbled.detail ?? "", /^tool failure: the producer's --explain printed a malformed explanation/);
  // An operational failure of the verifier is its own exit status, 3.
  const unread = tested(verifierCall(verifier, ["--lower-control-flow", join(dir, "absent.json")]));
  assert.equal(unread.status, 3, unread.stderr);
  assert.match(unread.stderr, /^error: /);
  process.stdout.write("step failures: an exit without a complete refusal, and a failed --explain, are tool failures\n");
});

control(async (): Promise<void> => {
  // A receiver is narrowed only past a read of it that completes on every
  // path: each negative's claims, forged to state `d` without `undefined` at
  // its `return d;`, are refused at that statement's incoming edge, whatever
  // the producer proposed.
  for (const name of ["optional", "write", "alias", "catch", "branch", "and", "expression-write", "loop", "finally", "join"]) {
    const file = `invalid-read-narrows-${name}`;
    const artifacts = run(file);
    const source = readFileSync(sourceKey(artifacts), "utf8");
    const claims = readClaims(artifacts);
    const fn = must(claims.functions.find(f => f.name === "wrong"), `${file}: wrong`);
    const entry = must(fn.entries.find(e => source.startsWith("return d;", e.start)), `${file}: return d;`);
    const d = must(entry.bindings.find(b => b.name === "d"), `${file}: d`);
    const undefinedRow = claims.types.findIndex(row => JSON.stringify(row) === JSON.stringify(["undef"]));
    const labels = d.type;
    assert.ok(Array.isArray(labels), `${file}: d's claim is a union of labels`);
    const narrowed = labels.filter(label => label !== undefinedRow);
    assert.ok(narrowed.length < labels.length, `${file}: d admits undefined at return d;`);
    d.type = narrowed;
    // The returned read of `d` claimed narrowed too, so that only the edge
    // into the statement is left to refuse.
    const read = must(fn.expressions.find(e => e.pos[0] === entry.start + "return ".length &&
      e.pos[1] === entry.start + "return d".length), `${file}: the returned d`);
    read.type = narrowed;
    const input = writeClaims(artifacts, `forged-read-narrows-${name}`, claims);
    refusedAt(artifacts, input, `forged-read-narrows-${name}`,
      `source incoming edge obligation at [${entry.start},${entry.start + "return d;".length})`);
  }
  process.stdout.write("read narrowing: a receiver claimed narrowed past no completed read is refused at the edge, in 10 negatives\n");
});

control(async (): Promise<void> => {
  // A negated `||` of tests states no obligation of its operand apart from
  // the evaluation's nodes, and a negation its operand decides keeps that
  // answer: claims forged past what those nodes establish are refused, in
  // search and in checking against the genuine evidence. The second test's
  // read claimed without the value the first test's failure leaves it; the
  // negation claimed `true` or a nonempty wrong-kind type in a condition
  // and as the left operand of `&&`.
  const artifacts = run("negated-disjunction-test");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const spanOf = (text: string, from: string): [number, number] => {
    const start = source.indexOf(text, source.indexOf(from));
    assert.ok(start >= 0, text);
    return [start, start + text.length];
  };
  const forge = (name: string, fnName: string, span: [number, number], row: Row): void => {
    const claims = readClaims(artifacts);
    const fn = must(claims.functions.find(f => f.name === fnName), `${fnName}'s claims`);
    const claim = must(fn.expressions.find(e => e.pos[0] === span[0] && e.pos[1] === span[1]),
      `${fnName}: the claim at [${span[0]},${span[1]})`);
    claim.type = [rowOf(claims, row[0])];
    const forged = writeClaims(artifacts, name, claims);
    const searched = produceWith(artifacts, forged, name);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    invoke(forged, join(artifacts, "evidence.json"), artifacts);
  };
  const negation = '!(k.name === "a" || k.name === "b")';
  forge("forged-negated-disjunction-read", "rest", spanOf("k.name", 'k.name === "b"'), [{ strIn: { values: ["c", "d"] } }]);
  forge("forged-negated-disjunction-condition", "rest", spanOf(negation, "export function rest"),
    [{ boolLit: { value: true } }]);
  forge("forged-negated-disjunction-operand", "operand", spanOf(negation, "export function operand"),
    [{ boolLit: { value: true } }]);
  forge("forged-negated-disjunction-number", "rest", spanOf(negation, "export function rest"),
    [{ numLit: { bits: "0" } }]);
  forge("forged-negated-disjunction-string", "operand", spanOf(negation, "export function operand"),
    [{ strLit: { value: "x" } }]);
  process.stdout.write("negated disjunction: a re-read claimed past the first test's answer, and a negation claimed true or at a nonempty wrong-kind type, refused in search and in checking\n");
});

mutationControl(async (): Promise<void> => {
  // Constant returns isolate the entry obligation from subsequent read typing.
  // Forged claims select named paths at source statements. The test-only
  // mutation executable searches their complete evidence and checks it with
  // every selected bypass necessary: coverage, links, or cell knowledge.
  // A write of a `let` slot root rebinds the slot, so no link from it
  // reaches an entry after the write (`afterRoot`) or a loop head the
  // write's back edge enters (`backEdge`) (HOST-FAMILIES.md, "Paths rooted
  // at a slot").
  const artifacts = run("path-witness-controls");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const honest = readClaims(artifacts);
  const before = must(honest.functions.find(f => f.name === "before"), "witness before");
  const refined = must(before.entries.find(e => source.startsWith("return 1;", e.start)), "refined entry");
  const current = must(must(refined.bindings.find(b => b.name === "holder"), "holder").current, "witness type");
  const type = must(current.find(([[field]]) => field === "value"), "value field")[1];
  const object = (value: unknown): value is Record<string, unknown> =>
    typeof value === "object" && value !== null && !Array.isArray(value);
  for (const [name, functionName, marker, failure] of [
    ["before", "before", "if (holder.value", "type coverage"],
    ["afterCall", "afterCall", "return 0;", "heap knowledge"],
    ["afterRoot", "afterRoot", "return 0;", "heap knowledge"],
    ["backEdge", "backEdge", "while (n < limit)", "type coverage"],
    ["caught", "caught", "return /* caught */ 0;", "heap knowledge"],
    ["predecessor", "before", "return 0;", "type coverage"],
    ["read", "afterCallRead", "return holder.value;", "heap knowledge"],
  ]) {
    const claims = structuredClone(honest);
    const fn = must(claims.functions.find(f => f.name === functionName), name);
    const at = must(fn.entries.filter(e => source.startsWith(marker, e.start)).sort((a, b) => a.start - b.start)[0], `${name}: forged entry`);
    must(at.bindings.find(b => b.name === "holder"), "holder").current = [[["value"], type]];
    if (name === "read") {
      const expression = must(fn.expressions.find(e => e.pos[0] === at.start + "return ".length &&
        e.pos[1] === at.start + "return holder.value".length), "read past call");
      expression.type = type;
    }
    const input = writeClaims(artifacts, `forged-witness-${name}`, claims);
    const obligation = `source incoming edge obligation at [${at.start},${name === "backEdge" ? source.indexOf("}", at.start) + 1 : source.indexOf(";", at.start) + 1})`;
    refusedAt(artifacts, input, `forged-witness-${name}`, obligation);
    const checked = invoke(input, forgedEvidence(artifacts, input, `forged-witness-${name}`,
      name === "predecessor" ? "coverage" : name === "afterCall" || name === "read" ? "links" :
        name === "afterRoot" ? "links" : "coverage,links"), artifacts);
    assert.ok(checked.includes(`${obligation}: evidence fails ${failure} from node `), checked);
  }

  // Both paths have been read and refined to the same type. The false relation
  // is added at a non-cut return node, so the source entry's exact interface
  // stays intact. Its output carries the same added link in the pushed frame.
  // Only the incoming read-link obligation can reject this evidence.
  type Link = { cell: number; value: number; alias: boolean; field: string; optional: boolean };
  type WitnessNode = WireNode & { knowledge: { links: Link[] }; output: { links: Link[] } };
  for (const name of ["receiver", "field"]) {
    const evidence: unknown = unfoldedEvidence(join(artifacts, "evidence.json"));
    assert.ok(object(evidence) && object(evidence.main) && Array.isArray(evidence.main.functions));
    const index = honest.functions.findIndex(f => f.name === name);
    const fn = must(honest.functions[index], name);
    const entry = must(fn.entries.find(e => source.startsWith("return 1;", e.start)), "both paths refined");
    for (const [root, field] of name === "receiver" ? [["holder", "value"], ["other", "value"]] : [["holder", "value"], ["holder", "other"]]) {
      const binding = must(entry.bindings.find(b => b.name === root), root);
      assert.deepEqual(must(binding.current, "refined path").find(([[f]]) => f === field)?.[1], type);
    }
    const unit: unknown = evidence.main.functions[index];
    assert.ok(object(unit) && Array.isArray(unit.certificate));
    const certificate = unit.certificate as WitnessNode[]; // asserted: honest verifier-produced evidence; Lean independently decodes the complete forged document
    const node = must(certificate.find(c => {
      const links = c.knowledge.links.filter(l => !l.alias);
      return JSON.stringify(nodeSequent(c).term) === JSON.stringify({ var: { i: 0 } }) &&
        links.length === 2 && links.every(l => l.cell > 0 && l.value > 0) &&
        JSON.stringify(nodeSequent(c).context[links[0].value]) === JSON.stringify(nodeSequent(c).context[links[1].value]);
    }), `${name}: two refined witnesses at a non-cut return`);
    const [first, second] = node.knowledge.links.filter(l => !l.alias);
    if (name === "receiver") {
      assert.notEqual(first.cell, second.cell);
      assert.equal(first.field, second.field);
    } else {
      assert.equal(first.cell, second.cell);
      assert.notEqual(first.field, second.field);
    }
    const forged = name === "receiver" ? { ...first, cell: second.cell } : { ...first, field: second.field };
    assert.ok(!node.knowledge.links.some(l => JSON.stringify(l) === JSON.stringify(forged)), "a false origin, not a duplicate link");
    node.knowledge.links.push(forged);
    node.output.links.push({ ...forged, cell: forged.cell + 1, value: forged.value + 1 });
    const path = join(artifacts, `forged-witness-${name}-evidence.json`);
    writeFileSync(path, tabledEvidence(evidence));
    checkMutation(artifacts, join(artifacts, "claims.json"), path, "links");
    const start = entry.start + "return ".length;
    const checked = invoke(join(artifacts, "claims.json"), path, artifacts);
    assert.ok(checked.includes(`source incoming edge obligation at [${start},${start + 1}): evidence fails heap knowledge`), checked);
  }
  // An alias link holds by an edge's mapping alone where the edge takes its
  // two slots from one source slot (`mapped-alias`, HeapLinks.check). In
  // `receiver`, a node's two slots of one type that its honest knowledge
  // relates by no alias are taken from different source slots, since the
  // producer states every mapped alias: an alias claimed between them is
  // refused by heap knowledge, and accepted with the links check bypassed.
  {
    const evidence: unknown = unfoldedEvidence(join(artifacts, "evidence.json"));
    assert.ok(object(evidence) && object(evidence.main) && Array.isArray(evidence.main.functions));
    const unit: unknown = evidence.main.functions[honest.functions.findIndex(f => f.name === "receiver")];
    assert.ok(object(unit) && Array.isArray(unit.certificate));
    const certificate = unit.certificate as WitnessNode[]; // asserted: honest verifier-produced evidence; Lean independently decodes the complete forged document
    const aliased = (node: WitnessNode, i: number, j: number): boolean =>
      node.knowledge.links.some(l => l.alias && ((l.cell === i && l.value === j) || (l.cell === j && l.value === i)));
    // A slot copy's output is its knowledge past the result, so the forged
    // link's image there is the link one slot on, for slots other than the
    // copied one.
    const copied = (node: WitnessNode): number | null => {
      const term = nodeSequent(node).term;
      return object(term) && object(term.var) && typeof term.var.i === "number" ? term.var.i : null;
    };
    const pairs = certificate.slice(1).flatMap(node => {
      const slot = copied(node);
      const context = nodeSequent(node).context.map(t => JSON.stringify(t));
      return slot === null ? [] : context.flatMap((t, i) => context.flatMap((u, j) =>
        i < j && t === u && i !== slot && j !== slot && !aliased(node, i, j) ? [{ node, i, j }] : []));
    });
    const { node, i, j } = must(pairs[0], "receiver: two unaliased slots of one type");
    const forged: Link = { cell: i, value: j, alias: true, field: "value", optional: false };
    node.knowledge.links.push(forged);
    node.output.links.push({ ...forged, cell: i + 1, value: j + 1 });
    const path = join(artifacts, "forged-mapped-alias-evidence.json");
    writeFileSync(path, tabledEvidence(evidence));
    checkMutation(artifacts, join(artifacts, "claims.json"), path, "links");
    const checked = invoke(join(artifacts, "claims.json"), path, artifacts);
    assert.ok(checked.includes("evidence fails heap knowledge"), checked);
  }
  process.stdout.write("path witnesses: exact forged evidence refused at incoming edges; wrong receiver/field isolate links, false predecessor isolates type coverage, an alias of slots from two sources isolates links\n");
});

mutationControl(async (): Promise<void> => {
  // Separation facts (HeapSeparation): an argument stated fresh, a level at
  // its depth, and a separation at a depth one off (its levels naming other
  // slots) are each refused by heap knowledge at the edge entering the node,
  // and accepted with that check bypassed (`separation`). Without the cell's
  // explicit fact, the body's evidence is refused.
  const artifacts = run("fresh-separation");
  const honest = readClaims(artifacts);
  const object = (value: unknown): value is Record<string, unknown> =>
    typeof value === "object" && value !== null && !Array.isArray(value);
  type Fact = { slot: number; fields: string[] | null; partners: [number, string[]][] };
  type Separation = { depth: number; facts: Fact[] };
  type SeparationNode = WireNode & { knowledge: { separation: Separation }; output: { separation: Separation } };
  const certificate = (evidence: unknown, name: string): SeparationNode[] => {
    assert.ok(object(evidence) && object(evidence.main) && Array.isArray(evidence.main.functions));
    const unit: unknown = evidence.main.functions[honest.functions.findIndex(f => f.name === name)];
    assert.ok(object(unit) && Array.isArray(unit.certificate));
    return unit.certificate as SeparationNode[]; // asserted: honest verifier-produced evidence; Lean independently decodes the complete forged document
  };
  // A node pushing a sum past a separation, whose output is its knowledge
  // one push deeper: the same facts.
  const pushing = (c: SeparationNode[]): SeparationNode => must(c.find(n => {
    const term = nodeSequent(n).term;
    return n.knowledge.separation.facts.length > 0 && n.effect !== null && "pure" in n.effect &&
      object(term) && "arith" in term && n.output.separation.depth === n.knowledge.separation.depth + 1;
  }), "a sum pushed past a separation");
  const edits: [string, (n: SeparationNode) => void][] = [
    // The argument `x` (level 1) as if fresh, apart from its own field: no
    // allocation states it.
    ["argument-fresh", (n) => {
      const fact: Fact = { slot: 1, fields: null, partners: [[1, ["value"]]] };
      n.knowledge.separation.facts.push(fact);
      n.output.separation.facts.push(fact);
    }],
    // A level at the depth names no slot.
    ["out-of-range", (n) => {
      const fact: Fact = { slot: n.knowledge.separation.depth, fields: null, partners: [[0, ["value"]]] };
      n.knowledge.separation.facts.push(fact);
      n.output.separation.facts.push(fact);
    }],
    // One deeper, every level names the slot below the one it named.
    ["stale-depth", (n) => {
      n.knowledge.separation.depth += 1;
      n.output.separation.depth += 1;
    }],
  ];
  for (const [name, edit] of edits) {
    const evidence: unknown = unfoldedEvidence(join(artifacts, "evidence.json"));
    edit(pushing(certificate(evidence, "loopCells")));
    const path = join(artifacts, `forged-separation-${name}-evidence.json`);
    writeFileSync(path, tabledEvidence(evidence));
    checkMutation(artifacts, join(artifacts, "claims.json"), path, "separation");
    const checked = invoke(join(artifacts, "claims.json"), path, artifacts);
    assert.ok(checked.includes("evidence fails heap knowledge"), `${name}: ${checked}`);
  }
  // The cell's explicit fact, the residual the lowering states at each
  // statement entry, removed from every node of the body: the knowledge
  // stays consistent from edge to edge, and a node's stated output keeps
  // what the separation left no longer establishes.
  {
    const evidence: unknown = unfoldedEvidence(join(artifacts, "evidence.json"));
    const c = certificate(evidence, "loopCells");
    const explicit = (f: Fact): boolean => f.fields !== null;
    assert.ok(c.some(n => n.knowledge.separation.facts.some(explicit)), "a cell's explicit fact");
    for (const n of c)
      for (const k of [n.knowledge, n.output]) k.separation.facts = k.separation.facts.filter(f => !explicit(f));
    const path = join(artifacts, "forged-separation-residual-evidence.json");
    writeFileSync(path, tabledEvidence(evidence));
    const checked = invoke(join(artifacts, "claims.json"), path, artifacts);
    assert.match(checked, /source evidence refusal at \[\d+,\d+\): the evidence does not establish this node's/);
  }
  process.stdout.write("separation: an argument stated fresh, a level at its depth and a stale depth isolate the separation check; without its cell's explicit fact the body's evidence is refused\n");
});

mutationControl(async (): Promise<void> => {
  // Paths of two members at a statement entry (HOST-FAMILIES.md, "Entries"):
  // the witness of `holder.mid.leaf` is read from the witness of
  // `holder.mid` through `leaf`, and every incoming edge checks that second
  // segment's link as it checks the first's. The honest document, the
  // neighbour of each forged one, is accepted. A forged entry claim at an
  // unjustified predecessor is refused by type coverage, one past a call by
  // the links the call ends; a forged second-segment link of another
  // receiver or another field is refused by heap knowledge. Each forged
  // document is accepted with exactly the check it isolates disabled.
  const artifacts = run("path-chain-controls");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const honest = readClaims(artifacts);
  const accepted = tested(verifierCall(verifier, ["--check-source-claims", join(artifacts, "fragment.json"), join(artifacts, "claims.json"),
    sourceKey(artifacts), join(artifacts, "evidence.json")]));
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const chain = (path: readonly string[]): boolean => path.length === 2 && path[0] === "mid" && path[1] === "leaf";
  const before = must(honest.functions.find(f => f.name === "before"), "chain before");
  const refined = must(before.entries.find(e => source.startsWith("return 1;", e.start)), "chain refined entry");
  const current = must(must(refined.bindings.find(b => b.name === "holder"), "holder").current, "chain witness type");
  const type = must(current.find(([path]) => chain(path)), "the two-member path")[1];
  for (const [name, functionName, marker, failure, mutations] of [
    ["predecessor", "before", "return 0;", "type coverage", "coverage"],
    ["afterCall", "afterCall", "return 0;", "heap knowledge", "links"],
  ]) {
    const claims = structuredClone(honest);
    const fn = must(claims.functions.find(f => f.name === functionName), name);
    const at = must(fn.entries.filter(e => source.startsWith(marker, e.start)).sort((a, b) => a.start - b.start)[0], `${name}: forged chain entry`);
    must(at.bindings.find(b => b.name === "holder"), "holder").current = [[["mid", "leaf"], type]];
    const input = writeClaims(artifacts, `forged-chain-${name}`, claims);
    const obligation = `source incoming edge obligation at [${at.start},${source.indexOf(";", at.start) + 1})`;
    refusedAt(artifacts, input, `forged-chain-${name}`, obligation);
    const checked = invoke(input, forgedEvidence(artifacts, input, `forged-chain-${name}`, mutations), artifacts);
    assert.ok(checked.includes(`${obligation}: evidence fails ${failure} from node `), checked);
  }

  // A second-segment link, from a prefix's witness to the path's, added at
  // a non-cut return node beside the honest ones: of the other prefix's
  // witness (`receiver`), or through the prefix's other field (`field`).
  type Link = { cell: number; value: number; alias: boolean; field: string; optional: boolean };
  type WitnessNode = WireNode & { knowledge: { links: Link[] }; output: { links: Link[] } };
  const object = (value: unknown): value is Record<string, unknown> =>
    typeof value === "object" && value !== null && !Array.isArray(value);
  for (const name of ["receiver", "field"]) {
    const evidence: unknown = unfoldedEvidence(join(artifacts, "evidence.json"));
    assert.ok(object(evidence) && object(evidence.main) && Array.isArray(evidence.main.functions));
    const index = honest.functions.findIndex(f => f.name === name);
    const fn = must(honest.functions[index], name);
    const entry = must(fn.entries.find(e => source.startsWith("return 1;", e.start)), "both chains refined");
    const second = name === "receiver" ? ["alt", "leaf"] : ["mid", "other"];
    const binding = must(entry.bindings.find(b => b.name === "holder"), "holder");
    for (const path of [["mid", "leaf"], second])
      assert.deepEqual(must(binding.current, "refined chains").find(([p]) => p.join(".") === path.join("."))?.[1], type);
    const unit: unknown = evidence.main.functions[index];
    assert.ok(object(unit) && Array.isArray(unit.certificate));
    const certificate = unit.certificate as WitnessNode[]; // asserted: honest verifier-produced evidence; Lean independently decodes the complete forged document
    // The second segments: links whose receiver is the value of another link.
    const segments = (c: WitnessNode): Link[] => {
      const links = c.knowledge.links.filter(l => !l.alias);
      return links.filter(l => links.some(r => r.value === l.cell));
    };
    const node = must(certificate.find(c => {
      const links = segments(c);
      return JSON.stringify(nodeSequent(c).term) === JSON.stringify({ var: { i: 0 } }) &&
        links.length === 2 && links.every(l => l.cell > 0 && l.value > 0) &&
        JSON.stringify(nodeSequent(c).context[links[0].value]) === JSON.stringify(nodeSequent(c).context[links[1].value]);
    }), `${name}: two refined chains at a non-cut return`);
    const [first, other] = segments(node);
    if (name === "receiver") {
      assert.notEqual(first.cell, other.cell);
      assert.equal(first.field, other.field);
    } else {
      assert.equal(first.cell, other.cell);
      assert.notEqual(first.field, other.field);
    }
    const forged = name === "receiver" ? { ...first, cell: other.cell } : { ...first, field: other.field };
    assert.ok(!node.knowledge.links.some(l => JSON.stringify(l) === JSON.stringify(forged)), "a false origin, not a duplicate link");
    node.knowledge.links.push(forged);
    node.output.links.push({ ...forged, cell: forged.cell + 1, value: forged.value + 1 });
    const path = join(artifacts, `forged-chain-${name}-evidence.json`);
    writeFileSync(path, tabledEvidence(evidence));
    checkMutation(artifacts, join(artifacts, "claims.json"), path, "links");
    const start = entry.start + "return ".length;
    const checked = invoke(join(artifacts, "claims.json"), path, artifacts);
    assert.ok(checked.includes(`source incoming edge obligation at [${start},${start + 1}): evidence fails heap knowledge`), checked);
  }
  process.stdout.write("path chains: the honest document accepted; a forged predecessor refused by type coverage, a chain past a call and a second segment's wrong receiver or field by heap knowledge, each accepted with that check disabled\n");
});

// Each forged claim is a control of its own: each executes a search and a
// check, and the mutation verifier's search and checks.
for (const variant of ["covered", "kept", "taken"] as const) mutationControl(async (): Promise<void> => {
  // A guard's false edge over tag-set arms (PROGRAM-TYPING.md, "A
  // membership test", member-split). Over `Node`, where `isToken` answers
  // false, the claim the checker accepts names no `Token` application. At
  // a constant return past each guard's false edge, a forged claim of the
  // arm `isToken` covers alone, and one reading the split arm at the tag
  // `isDotToken` took out, are refused by type coverage, in search and in
  // checking, each accepted with that check disabled; their neighbours, the
  // honest claims and a claim keeping the covered arm beside the computed
  // name, are accepted.
  const artifacts = run("compiler-api-guard-false-sets");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const honest = readClaims(artifacts);
  const fragment = readFragmentFile(join(artifacts, "fragment.json"));
  const names = must(fragment.declarations, "the declarations").definitions.map(d => d.declaration.name);
  const declOf = (name: string): number => {
    const i = names.indexOf(name);
    assert.ok(i >= 0, name);
    return i;
  };
  const entryOf = (claims: SourceClaims, fn: string, marker: string) => {
    const unit = must(claims.functions.find(f => f.name === fn), fn);
    const from = source.indexOf(`function ${fn}(`);
    return must(unit.entries.filter(e => e.start > from && source.startsWith(marker, e.start))
      .sort((a, b) => a.start - b.start)[0], `${fn}: ${marker}`);
  };
  const nOf = (claims: SourceClaims, fn: string, marker: string) =>
    must(entryOf(claims, fn, marker).bindings.find(b => b.name === "n"), `${fn}: n`);
  const token = declOf("Token");
  const anyNode = nOf(honest, "anyNode", "return n.pos;").type;
  assert.ok(Array.isArray(anyNode) && !JSON.stringify(anyNode).includes(`{"decl":${token}`), JSON.stringify(anyNode));
  const split = nOf(honest, "afterDotConstant", "return 1;").type;
  assert.ok(Array.isArray(split) && split.some(l => typeof l === "object" && "decl" in l && l.decl === token), JSON.stringify(split));
  const computed = { decl: declOf("ComputedPropertyName") };
  const punctuation = { decl: declOf("Punctuation") };
  for (const [name, fn, type, accepted] of [
    ["covered", "nonTokenConstant", [punctuation], false],
    ["kept", "nonTokenConstant", [computed, punctuation], true],
    ["taken", "afterDotConstant", "dot", false],
  ] as const) {
    if (name !== variant) continue;
    const claims = structuredClone(honest);
    const at = entryOf(claims, fn, "return 1;");
    const binding = must(at.bindings.find(b => b.name === "n"), "n");
    binding.type = type === "dot"
      ? [{ decl: token, args: [[rowOf(claims, { numLit: { bits: "4627448617123184640" } })]] }, computed]
      : [...type];
    const input = writeClaims(artifacts, `forged-false-set-${name}`, claims);
    if (accepted) {
      const searched = produceWith(artifacts, input, `forged-false-set-${name}`);
      assert.equal(searched.status, 0, searched.stdout + searched.stderr);
      continue;
    }
    // The search reports one of the guard node's two edges.
    const obligation = `source incoming edge obligation at [${at.start},${at.start + "return 1;".length})`;
    const truthy = entryOf(claims, fn, "return 0;");
    const searched = produceWith(artifacts, input, `forged-false-set-${name}`);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    assert.ok([obligation, `source incoming edge obligation at [${truthy.start},${truthy.start + "return 0;".length})`]
      .some(o => (searched.stdout + searched.stderr).includes(o)), searched.stdout + searched.stderr);
    const checked = invoke(input, forgedEvidence(artifacts, input, `forged-false-set-${name}`, "coverage"), artifacts);
    assert.ok(checked.includes(`${obligation}: evidence fails type coverage from node `), checked);
  }
  process.stdout.write({
    covered: "tag-set false edges: no Token arm past isToken over Node; a claim of the covered arm alone refused in search and checking, accepted with coverage disabled\n",
    kept: "tag-set false edges: a claim keeping the covered arm beside the computed name accepted\n",
    taken: "tag-set false edges: a claim of the tag isDotToken took out refused in search and checking, accepted with coverage disabled\n",
  }[variant]);
});

control(async (): Promise<void> => {
  // Stable keys in the declaration document (HOST-FAMILIES.md, "Stable
  // keys"): the decoder accepts them as readonly members, required or
  // optional, of a marked family shape alone. Each forged document is
  // refused by the decoder; its neighbour, differing in the one thing the
  // check reads, is decoded.
  const artifacts = run("compiler-api-path-witness");
  type Definition = TypeDefinition;
  type ObjectTerm = Extract<TypeTerm, { k: "object" }>;
  const shapeOf = (d: Definition): ObjectTerm => {
    const e = d.expression;
    assert(e?.k === "object");
    return e;
  };
  const searchWith = (file: string, change: (o: ObjectTerm) => void): string => {
    const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
    const definition = must(must(fragment.declarations, "the declarations").definitions.find(d =>
      d.expression?.k === "object" && d.expression.host !== undefined && (d.expression.stable ?? []).length > 1 &&
      d.expression.fields.some(f => f.name === "text")), "a marked shape with stable keys");
    change(shapeOf(definition));
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    const searched = produceWith(artifacts, join(artifacts, "claims.json"), file, path);
    return searched.stdout + searched.stderr;
  };
  const decoder = /stable key/;
  const honest = searchWith("stable-honest", () => {});
  assert.doesNotMatch(honest, decoder, honest);
  // A writable member stated stable, optional and required; the neighbour
  // of each states the member readonly, which the optional one is decoded
  // as too.
  const writable = searchWith("forged-stable-writable", o => {
    const text = must(o.fields.find(f => f.name === "text"), "text");
    text.optional = true;
    text.readonly = false;
  });
  assert.match(writable, /the stable key "text" is no readonly member of its shape/, writable);
  const writableRequired = searchWith("forged-stable-writable-required", o => {
    must(o.fields.find(f => f.name === "text"), "text").readonly = false;
  });
  assert.match(writableRequired, /the stable key "text" is no readonly member of its shape/, writableRequired);
  const optionalNeighbour = searchWith("stable-optional-neighbour", o => {
    must(o.fields.find(f => f.name === "text"), "text").optional = true;
  });
  assert.doesNotMatch(optionalNeighbour, decoder, optionalNeighbour);
  // A key the shape does not state; its neighbour states the member.
  const absent = searchWith("forged-stable-absent", o => { o.stable = [...(o.stable ?? []), "noSuchMember"]; });
  assert.match(absent, /the stable key "noSuchMember" is no readonly member of its shape/, absent);
  const absentNeighbour = searchWith("stable-absent-neighbour", o => {
    const text = must(o.fields.find(f => f.name === "text"), "text");
    o.fields.push({ ...text, name: "noSuchMember" });
    o.stable = [...(o.stable ?? []), "noSuchMember"];
  });
  assert.doesNotMatch(absentNeighbour, decoder, absentNeighbour);
  // An unmarked shape stating stable keys, at a required member and at an
  // optional one, as a program record would; its neighbour states none.
  const unmarked = searchWith("forged-stable-unmarked", o => { delete o.host; });
  assert.match(unmarked, /a stable key is stated of a host family's marked shape alone/, unmarked);
  const unmarkedOptional = searchWith("forged-stable-unmarked-optional", o => {
    delete o.host;
    must(o.fields.find(f => f.name === "text"), "text").optional = true;
  });
  assert.match(unmarkedOptional, /a stable key is stated of a host family's marked shape alone/, unmarkedOptional);
  const unmarkedNeighbour = searchWith("stable-unmarked-neighbour", o => { delete o.host; delete o.stable; });
  assert.doesNotMatch(unmarkedNeighbour, decoder, unmarkedNeighbour);
  process.stdout.write("stable keys: a writable (optional and required), an absent and an unmarked (required and optional) stable key refused by the decoder, each beside its decoded neighbour, an optional readonly one decoded\n");
});

control(async (): Promise<void> => {
  // Claim admissibility (the claims decoder): a fact of a field is claimed
  // at a statement entry only where every record arm of the binding's type
  // names the field. The producer refuses a union with an arm lacking `kind`
  // (`invalid-guard-after-kind-missing`); claims widening the node at the
  // guard's entry by such an arm, the fact of `kind` kept, are refused by
  // search and by the checker at decoding, located at the entry. The
  // neighbour's arm states `kind` and decodes.
  const artifacts = run("compiler-api-guard-after-kind-tests");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const start = source.indexOf("if (ts.isParenthesizedExpression(node))");
  const forge = (name: string, withKind: boolean): string => {
    const claims = readClaims(artifacts);
    const fn = must(claims.functions.find((f) => f.name === "literal"), "literal's claims");
    const entry = must(fn.entries.find((e) => e.start === start), "the guard's entry");
    const node = must(entry.bindings.find((b) => b.name === "node"), "node at the guard");
    assert.ok(node.current?.some(([[key]]) => key === "kind"), "the fact of kind at the guard");
    const num = rowOf(claims, "num");
    const arm = rowOf(claims, { refs: { first: withKind ? [["kind", [num]], ["other", [num]]] : [["other", [num]]],
      rest: [], views: [] } });
    const declared = node.type;
    assert.ok(Array.isArray(declared), "node's labels at the guard");
    node.type = [arm, ...declared];
    return writeClaims(artifacts, name, claims);
  };
  const decoder = `invalid source claims: invalid current-contents field of 'node' at the entry at ${start}`;
  const missing = forge("forged-guard-kind-missing-arm", false);
  refusedAt(artifacts, missing, "forged-guard-kind-missing-arm", decoder);
  assert.ok(invoke(missing, join(artifacts, "evidence.json"), artifacts).includes(decoder));
  const neighbour = forge("guard-kind-stated-arm", true);
  const searched = produceWith(artifacts, neighbour, "guard-kind-stated-arm");
  assert.ok(!(searched.stdout + searched.stderr).includes(decoder), searched.stdout + searched.stderr);
  process.stdout.write("guard after kind tests: a fact of kind at a receiver with an arm lacking kind refused by the claims decoder in search and check, its neighbour stating kind decoded\n");
});

mutationControl(async (): Promise<void> => {
  // The presence decision of `read-observed-present` alone: the guard's
  // reread of `kind`, answered by the fact the failed tests leave, links its
  // result presently since `Node` states `kind`, and the guard's true edge
  // narrows the node through that link. The test-only verifier withholding
  // it (`absent`: the read's link optional whatever the receiver's type
  // states) refuses the same claims in search at the guard's true edge and
  // the honest evidence at the guard; without the mutation it accepts both.
  const artifacts = run("compiler-api-guard-after-kind-tests");
  const source = readFileSync(sourceKey(artifacts), "utf8");
  const ret = source.indexOf("return literal(node.expression);");
  const guard = source.indexOf("ts.isParenthesizedExpression(node)");
  const claims = join(artifacts, "claims.json");
  const call = (args: string[], mutations: string): Invoked =>
    tested(verifierCall(mutationVerifier(), args, { TSCERT_TEST_MUTATIONS: mutations }));
  const search = (mutations: string): Invoked => call(["--produce-source-claims", join(artifacts, "fragment.json"),
    claims, sourceKey(artifacts), join(artifacts, `presence-${mutations || "none"}-evidence.json`), "12"], mutations);
  const check = (mutations: string): Invoked => call(["--check-source-claims", join(artifacts, "fragment.json"),
    claims, sourceKey(artifacts), join(artifacts, "evidence.json")], mutations);
  const words = (p: Invoked): string => p.stdout + p.stderr;
  const plain = search("");
  assert.equal(plain.status, 0, words(plain));
  const withheld = search("absent");
  assert.equal(withheld.status, 1, words(withheld));
  assert.ok(words(withheld).includes(
    `source incoming edge obligation at [${ret},${ret + "return literal(node.expression);".length})`), words(withheld));
  const accepted = check("");
  assert.equal(accepted.status, 0, words(accepted));
  const refused = check("absent");
  assert.equal(refused.status, 1, words(refused));
  assert.ok(words(refused).includes(
    `source evidence refusal at [${guard},${guard + "ts.isParenthesizedExpression(node)".length})`), words(refused));
  process.stdout.write("guard after kind tests: the observed read's present link withheld, search refused at the guard's true edge and the honest evidence at the guard; both accepted with it\n");
});

control(async (): Promise<void> => {
  // Stable links (HOST-FAMILIES.md, "Stable links"): a read link through a
  // member every arm states stable survives a call. The positive case's
  // document with the tested member's stable key dropped from its shape,
  // the one thing the rule reads, is refused in search with the case's own
  // claims and in checking with its own evidence, at the read past the call;
  // the honest document is accepted.
  const artifacts = run("compiler-api-stable-link");
  const forged = (file: string, keys: (stable: readonly string[]) => string[] | undefined): string => {
    const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
    for (const d of must(fragment.declarations, "the declarations").definitions) {
      const e = d.expression;
      if (e?.k !== "object" || e.host === undefined || e.stable === undefined) continue;
      if (!e.fields.some(f => f.name === "initializer")) continue;
      const next = keys(e.stable);
      if (next && next.length) e.stable = next;
      else delete e.stable;
    }
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    return path;
  };
  const honest = forged("stable-link-honest", s => [...s]);
  const accepted = tested(verifierCall(verifier, ["--check-source-claims", honest, join(artifacts, "claims.json"),
    sourceKey(artifacts), join(artifacts, "evidence.json")]));
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const unstable = forged("forged-stable-link", s => s.filter(k => k !== "name"));
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-stable-link", unstable);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /obligation at \[\d+,\d+\)/, searched.stdout + searched.stderr);
  const checked = invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, unstable);
  assert.match(checked, /refusal at \[\d+,\d+\)|obligation at \[\d+,\d+\)/, checked);
  process.stdout.write("stable links: the document without the tested member's stable key refused in search and in checking, the honest one accepted\n");
});

control(async (): Promise<void> => {
  // Stable optional members (HOST-FAMILIES.md, "Stable keys"): the read of
  // an optional member past a call, absent or present, rests on the member's
  // stable key alone. The positive case's document with `initializer` and
  // `expression` dropped from the stable keys of the shapes stating them, the
  // one thing the rule reads, is refused in search with the case's own
  // claims and in checking with its own evidence; the honest document is
  // accepted.
  const artifacts = run("compiler-api-stable-optional");
  const forged = (file: string, keep: (key: string) => boolean): string => {
    const fragment: Ast = readFragmentFile(join(artifacts, "fragment.json"));
    for (const d of must(fragment.declarations, "the declarations").definitions) {
      const e = d.expression;
      if (e?.k !== "object" || e.host === undefined || e.stable === undefined) continue;
      const next = e.stable.filter(keep);
      if (next.length) e.stable = next;
      else delete e.stable;
    }
    const path = join(artifacts, `${file}.json`);
    writeFileSync(path, JSON.stringify(fragment));
    return path;
  };
  const honest = forged("stable-optional-honest", () => true);
  const accepted = tested(verifierCall(verifier, ["--check-source-claims", honest, join(artifacts, "claims.json"),
    sourceKey(artifacts), join(artifacts, "evidence.json")]));
  assert.equal(accepted.status, 0, accepted.stdout + accepted.stderr);
  const unstable = forged("forged-stable-optional", k => k !== "initializer" && k !== "expression");
  const searched = produceWith(artifacts, join(artifacts, "claims.json"), "forged-stable-optional", unstable);
  assert.equal(searched.status, 1, searched.stdout + searched.stderr);
  assert.match(searched.stdout + searched.stderr, /obligation at \[\d+,\d+\)/, searched.stdout + searched.stderr);
  const checked = invoke(join(artifacts, "claims.json"), join(artifacts, "evidence.json"), artifacts, unstable);
  assert.match(checked, /refusal at \[\d+,\d+\)|obligation at \[\d+,\d+\)/, checked);
  process.stdout.write("stable optional members: the document without the optional members' stable keys refused in search and in checking, the honest one accepted\n");
});

mutationControl(async (): Promise<void> => {
  // The constant-return neighbour supplies valid claims and evidence before
  // the tested call. Only the final path/read and its entry witness are forged;
  // the declaration document is identical throughout. The let-cell neighbour
  // observes the mutable root directly with a kind test; the original let
  // case also loses its member witness at a statement entry before the call.
  // The mutation executable searches the source-anchored claims. Each exact
  // document must pass its mutation and fail both the production verifier
  // and the other stable/handler mutation.
  for (const kind of ["mixed", "record", "let", "catch"] as const) {
    const artifacts = run(`invalid-compiler-api-stable-${kind === "let" ? "let-cell" : kind}`);
    const fragment = readFragmentFile(join(artifacts, "fragment.json"));
    const source = readFileSync(sourceKey(artifacts), "utf8");
    const body = must(fragment.functions[0], "the function").body;
    // Select the catch from the parsed tree, never from a keyword in a comment.
    const caught = body.find(s => s.k === "try");
    const handler = caught?.k === "try" ? caught.handler?.body[0] : undefined;
    if (kind === "catch") {
      assert.ok(handler?.k === "return");
      assert.deepEqual(handler.pos, [405, 424]);
    }
    const statement = kind === "catch" ? must(handler, "the handler entry")
      : must(body.find(s => s.k === "return"), "the final return");
    assert.ok(statement.k === "return" && statement.e);
    const returned = statement.e;
    const comma = returned.k === "conditional" ? returned.then : undefined;
    if (kind === "record" || kind === "let") assert.ok(comma?.k === "comma");
    const read = comma?.k === "comma" ? comma.right : returned;
    assert.ok(read.k === "read" && read.field === "text" && (read.e.k === "read" || read.e.k === "id"));
    const path = read.e;
    const [at, end] = read.pos;
    const neutral: Expr = { k: "lit", pos: read.pos, lit: { a: "stringlit", v: "" } };
    if (comma?.k === "comma") comma.right = neutral;
    else statement.e = neutral;
    const neighbour = join(artifacts, "stable-neighbour.json");
    writeFileSync(neighbour, JSON.stringify(fragment));
    const lowered = tested(verifierCall(verifier, ["--lower-control-flow", neighbour]));
    assert.equal(lowered.status, 0, lowered.stdout + lowered.stderr);
    const flow = join(artifacts, "stable-neighbour-flow.json");
    writeFileSync(flow, lowered.stdout);
    const proposed = tested(producerCall(producerExecutable, [neighbour, flow]));
    assert.equal(proposed.status, 0, proposed.stdout + proposed.stderr);
    const honestPath = join(artifacts, "stable-neighbour-claims.json");
    writeFileSync(honestPath, proposed.stdout);
    const claims = readClaimsFile(honestPath);
    const fn = must(claims.functions[0], "the claims");
    // The constant has the same (wider) result contract as the hostile read,
    // keeping the surrounding contexts and graph labels identical.
    for (const e of fn.expressions) if (e.pos[0] <= at && e.pos[1] >= end) e.type = fn.result;
    writeFileSync(honestPath, JSON.stringify(claims));
    const honestSearch = produceWith(artifacts, honestPath, "stable-neighbour", neighbour);
    assert.equal(honestSearch.status, 0, honestSearch.stdout + honestSearch.stderr);
    const constant = must(fn.expressions.find(e => e.pos[0] === at && e.pos[1] === end), "constant neighbour");
    const definitions = must(fragment.declarations, "declarations").definitions;
    const identifier = definitions.findIndex(d => d.declaration.name === "Identifier");
    assert.ok(identifier >= 0);
    const refined = [{ decl: identifier }];
    const prefix = structuredClone(fn.expressions.filter(e => e.pos[1] <= at));
    fn.expressions = fn.expressions.filter(e => e !== constant);
    // Copy each receiver's type from the honest pre-test read of the same path.
    const addRead = (e: Expr): void => {
      assert.ok(e.k === "read" || e.k === "id");
      if (e.k === "read") addRead(e.e);
      const previous = must(prefix.find(p => p.pos[1] - p.pos[0] === e.pos[1] - e.pos[0] &&
        source.slice(p.pos[0], p.pos[1]) ===
        source.slice(e.pos[0], e.pos[1])), "honest receiver read");
      fn.expressions.push({ ...structuredClone(previous), point: constant.point, pos: e.pos,
        type: e === path ? refined : previous.type, current: null });
    };
    addRead(path);
    fn.expressions.push({ ...constant, type: fn.result });
    for (const e of fn.expressions) if (e.pos[0] <= at && e.pos[1] >= end) e.type = fn.result;
    if (kind === "mixed" || kind === "catch") {
      const entry = must(fn.entries.find(e => e.start === statement.pos[0]), "post-call/handler entry");
      assert.equal(entry.start, kind === "catch" ? 405 : 500);
      must(entry.bindings.find(b => b.name === "m"), "m at the entry").current = [[["name"], refined]];
    }
    assert.deepEqual(fn.expressions.filter(e => e.pos[1] <= at), prefix);
    const forged = writeClaims(artifacts, `isolated-stable-${kind}`, claims);
    const searched = produceWith(artifacts, forged, `isolated-stable-${kind}`);
    assert.equal(searched.status, 1, searched.stdout + searched.stderr);
    const obligation = kind === "mixed" ? "source incoming edge obligation at [500,519)"
      : kind === "catch" ? "source expression obligation at [382,387)"
        : `source expression obligation at [${path.pos[0]},${path.pos[1]})`;
    assert.ok((searched.stdout + searched.stderr).includes(obligation), searched.stdout + searched.stderr);
    const evidencePath = forgedEvidence(artifacts, forged, `isolated-stable-${kind}`,
      kind === "catch" ? "handler" : "stable");
    const checked = invoke(forged, evidencePath, artifacts);
    if (kind === "catch")
      assert.match(checked, /source incoming edge obligation at \[405,424\): evidence fails heap knowledge from node \d+, handler edge/);
    else {
      // The forged output keeps the read link at the call. The exact output
      // check is the boundary that drops it, before any later read is checked.
      const callSpan = kind === "mixed" ? [491, 496] : kind === "record" ? [428, 433] : [495, 504];
      assert.ok(checked.includes(`source evidence refusal at [${callSpan[0]},${callSpan[1]}): the evidence does not establish this node's typing`), checked);
    }
  }
  process.stdout.write("stable-link negatives: honest pre-test claims and evidence; mixed, record and let isolate the call, catch isolates the incoming handler edge at [405,424)\n");
});

control(async (): Promise<void> => {
  // Replay: a cold run in a fresh store and a warm run in another run root
  // agree on their outcome, documents and logs; the warm run replays every
  // stage (module runs and explanations included), the parse by its
  // observations. The warm worker first checks other sources.
  // A changed source executes again.
  const store = runDirectory("tscert-replay-store-");
  const runAt = (source: string, project: string | null, preceding: readonly string[] = []): { outcome: Outcome; records: AttemptRecord[] } => {
    const root = runDirectory("tscert-replay-root-");
    // Sequential awaits use the same idle worker; each driver starts a fresh pool.
    const driver = `import { checkApart } from ${JSON.stringify(pathToFileURL(join(here, "verify-source.mts")).href)};
for (const source of ${JSON.stringify(preceding)}) await checkApart(source);
process.stdout.write(JSON.stringify(await checkApart(${JSON.stringify(source)}, ${JSON.stringify(project ?? undefined)})));`;
    const driverPath = join(root, "worker-history.mts");
    writeFileSync(driverPath, driver);
    const ran = spawnSync(process.execPath, [driverPath],
      { encoding: "utf8", timeout: 240_000, env: { ...process.env, TSCERT_STAGE_STORE: store, TSCERT_RUN_ROOT: root } });
    assert.equal(ran.status, 0, ran.stderr);
    const outcome = readOutcome(JSON.parse(ran.stdout.slice(ran.stdout.indexOf("{"))));
    return { outcome, records: readInvocationLog(join(outcome.artifacts, invocationLog)) };
  };
  const documents = ["fragment.json", "flow.json", "claims.json", "evidence.json", "parse.log", "flow.log",
    "proposal.log", "search.log", "check.log", "typescript-diagnostics.json"];
  const contents = (artifacts: string): Map<string, string> => new Map(documents.flatMap((name): [string, string][] =>
    present(join(artifacts, name)) ? [[name, readFileSync(join(artifacts, name), "utf8")]] : []));
  const replayed = new Set(["parse", "lower", "propose", "assemble", "search", "check", "explain", "diagnostics"]);
  const runs: [string, string | null][] = [["certified-nested-value-import", "pipeline/imports-project"],
    ["invalid-closure-contextual-result", null]];
  for (const [name, project] of runs) {
    const source = join(here, "examples", `${name}.ts`);
    const projectPath = project ? resolve(here, "..", project) : null;
    const cold = runAt(source, projectPath), warm = runAt(source, projectPath,
      [join(here, "examples", "values.ts"), join(here, "examples", "invalid-void-result.ts")]);
    const { artifacts: coldArtifacts, ...coldOutcome } = cold.outcome;
    const { artifacts: warmArtifacts, ...warmOutcome } = warm.outcome;
    assert.notEqual(coldArtifacts, warmArtifacts);
    assert.deepEqual(warmOutcome, coldOutcome, `${name}: the same outcome`);
    assert.deepEqual(contents(warmArtifacts), contents(coldArtifacts), `${name}: the same documents and logs`);
    // A replayed parse runs no stage nested in it: its imported modules' stages ran in the cold run only.
    const outer = (records: readonly AttemptRecord[]): string[] => records.filter((r) => r.stage !== "module").map((r) => r.stage);
    assert.deepEqual(outer(warm.records), outer(cold.records), `${name}: the same stages`);
    assert.ok(project === null || cold.records.some((r) => r.stage === "module"), `${name}: its modules' stages ran cold`);
    for (const r of cold.records) assert.ok(ranStage(r), `${name}: cold ${r.stage} executed`);
    for (const r of warm.records) {
      assert.equal(r.execution, replayed.has(r.stage) && r.key !== null ? "replayed" : "executed", `${name}: warm ${r.stage}`);
      if (replayed.has(r.stage) && r.key === null) {
        assert.match(r.ineligible ?? "", /macOS only|Node import, require or loader|Node DYLD_|confined on macOS/,
          `${name}: ${r.stage} explains its unidentified dependencies`);
        process.stdout.write(`${name}: ${r.stage} executes without a key: ${r.ineligible}\n`);
      }
    }
    assert.ok(warm.records.filter((r) => r.stage === "lower").length > (project ? 1 : 0), `${name}: module runs replayed`);
    assert.ok(project !== null || warm.records.some((r) => r.stage === "explain"), `${name}: its explanation replayed`);
  }
  const changed = join(runDirectory("tscert-replay-changed-"), "changed.ts");
  writeFileSync(changed, readFileSync(join(here, "examples", "values.ts"), "utf8") + "\n// changed\n");
  const before = runAt(join(here, "examples", "values.ts"), null);
  const after = runAt(changed, null);
  assert.equal(after.outcome.status, before.outcome.status);
  for (const r of after.records) assert.ok(ranStage(r), `a changed source: ${r.stage} executed`);
  process.stdout.write("replay: cold and warm workers with different request histories agree on outcomes, documents and logs; the warm run " +
    "replays every stage, the parse by its observations, and executes stages with unidentified dependencies; a changed source executes\n");
});

/** A control's result, as a control process reports it: its operations'
 * counts (`controlOperations`), and whether the process retires after it. */
type Operations = { executed: number; replayed: number; elapsedMs: number };
type Finished = { finished: number; error: string | null; operations: Operations; retiring: boolean };
const readFinished = (value: unknown): Finished => {
  const fail = (): never => {
    throw Error(`not a control's result: ${JSON.stringify(value)}`);
  };
  if (typeof value !== "object" || value === null || !("finished" in value) || typeof value.finished !== "number" ||
      !("error" in value) || !(value.error === null || typeof value.error === "string") || !("retiring" in value) ||
      typeof value.retiring !== "boolean" || !("operations" in value))
    return fail();
  const o = value.operations;
  if (typeof o !== "object" || o === null || !("executed" in o) || typeof o.executed !== "number" ||
      !("replayed" in o) || typeof o.replayed !== "number" || !("elapsedMs" in o) || typeof o.elapsedMs !== "number")
    return fail();
  return { finished: value.finished, error: value.error, retiring: value.retiring,
    operations: { executed: o.executed, replayed: o.replayed, elapsedMs: o.elapsedMs } };
};
if (serving) {
  // A control process: one control per message, with the mutation
  // verifier's path once it is built. A process whose caches may disagree
  // with the file system reports its control and exits; a fresh one takes
  // the next (STAGE-STORE.md, "Observed stages").
  useMutationVerifier(null);
  process.on("message", (message: unknown) => {
    if (typeof message !== "object" || message === null || !("control" in message) || typeof message.control !== "number" ||
        !("mutationVerifier" in message) || !(message.mutationVerifier === null || typeof message.mutationVerifier === "string"))
      throw Error(`not a control's request: ${JSON.stringify(message)}`);
    const index = message.control;
    if (message.mutationVerifier !== null) useMutationVerifier(message.mutationVerifier);
    const body = controls[index];
    if (body === undefined) throw Error(`no control ${index}`);
    const before = { ...controlOperations };
    const report = (error: string | null): void => {
      const retiring = processInconsistency() !== null || processRetirement() !== null;
      const finished: Finished = { finished: index, error, retiring, operations: {
        executed: controlOperations.executed - before.executed, replayed: controlOperations.replayed - before.replayed,
        elapsedMs: controlOperations.elapsedMs - before.elapsedMs } };
      process.send?.(finished, () => {
        if (retiring) process.exit(0);
      });
    };
    body().then(() => report(null), (error: unknown) =>
      report(error instanceof Error ? error.stack ?? error.message : String(error)));
  });
  process.on("disconnect", () => process.exit(0));
} else {
  linkFixtures();
  const started = performance.now();
  const failures: string[] = [];
  const tally: Operations = { executed: 0, replayed: 0, elapsedMs: 0 };
  // The controls not yet given: those running the mutation verifier join
  // once it is built. A lane with none to take waits for them.
  const pending = controls.flatMap((_, i) => mutationControls.has(i) ? [] : [i]);
  let mutationVerifier: string | null = null;
  const waiting: (() => void)[] = [];
  const mutationReady = must(mutationBuild, "the mutation verifier's build").then((built) => {
    assert.equal(built.status, 0, built.stdout + built.stderr);
    mutationVerifier = must(built.stdout.trim().split("\n").at(-1), "the mutation verifier's path");
    pending.unshift(...mutationControls);
    for (const wake of waiting.splice(0)) wake();
  });
  let processes = 0;
  const width = Math.min(availableParallelism(), controls.length);
  // One lane of the pool: a control process taking controls until none is
  // left, replaced by a fresh one where it retires.
  const lane = (): Promise<void> => new Promise<void>((done, fail) => {
    processes++;
    const child = fork(import.meta.filename, ["--controls"], { stdio: ["ignore", "pipe", "pipe", "ipc"] });
    // Each line a control prints, as it prints it.
    let printed = "", errors = "", retired = false;
    child.stdout?.setEncoding("utf8");
    child.stdout?.on("data", (text: unknown) => {
      printed += String(text);
      const at = printed.lastIndexOf("\n");
      if (at >= 0) {
        process.stdout.write(printed.slice(0, at + 1));
        printed = printed.slice(at + 1);
      }
    });
    child.stderr?.setEncoding("utf8");
    child.stderr?.on("data", (text: unknown) => { errors += String(text); });
    const give = (): void => {
      const index = pending.shift();
      if (index !== undefined) child.send({ control: index, mutationVerifier });
      else if (mutationVerifier === null) waiting.push(give);
      else child.disconnect();
    };
    child.on("message", (message: unknown) => {
      const result = readFinished(message);
      tally.executed += result.operations.executed;
      tally.replayed += result.operations.replayed;
      tally.elapsedMs += result.operations.elapsedMs;
      if (result.error !== null) failures.push(`control ${result.finished}: ${result.error}`);
      if (result.retiring) retired = true;
      else give();
    });
    child.on("error", fail);
    child.on("exit", (status: number | null) => {
      if (printed) process.stdout.write(printed + "\n");
      if (status !== 0) failures.push(`a control process exited with ${status}: ${errors}`);
      if (retired && status === 0 && (pending.length > 0 || mutationVerifier === null)) lane().then(done, fail);
      else done();
    });
    give();
  });
  await Promise.all([mutationReady, ...Array.from({ length: width }, lane)]);
  assert.deepEqual(failures, [], failures.join("\n"));
  const observed = await must(observedStages, "the observed stages' run");
  assert.equal(observed.status, 0, observed.stdout + observed.stderr);
  process.stdout.write(observed.stdout);
  const sessions = await must(sessionReuse, "the declaration sessions' run");
  assert.equal(sessions.status, 0, sessions.stdout + sessions.stderr);
  process.stdout.write(sessions.stdout);
  process.stdout.write(`controls: ${controls.length} in ${((performance.now() - started) / 1000).toFixed(1)} s on ${width} ` +
    `lanes (${processes} processes); their operations ${tally.executed} executed (${(tally.elapsedMs / 1000).toFixed(1)} s ` +
    `in all), ${tally.replayed} replayed\n`);
}
