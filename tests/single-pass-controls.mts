// The single pass's controls (`TSCERT_ROUTE=single-pass`, docs/drafts/single-pass.md):
// the inputs no case makes on the single-pass route, each control a block of
// this file run by a pool of control processes, one per core, every
// operation replayed from the stage store as pipeline/test.mts's controls'
// are (STAGE-STORE.md, "Controls"). A case is checked on the route (the
// parse, then `verifier --verify-interface-stage 8` with the interface
// stages it needs); a control then runs the pass over its fragment under a
// forced proposal (`TSCERT_FORCE`), or over a forged fragment, and requires
// the unit it names refused. The store-boundary controls of the interface
// stages name a fresh store.
import assert from "node:assert/strict";
import { mkdirSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { pathToFileURL } from "node:url";
import { join, resolve } from "node:path";
import { availableParallelism } from "node:os";
import { fork } from "node:child_process";
import { controlOperations, ran as ranStage, startEviction, type Invoked } from "../pipeline/stages.mts";
import { check as checkSource, readFragmentFile, sourceKey } from "../pipeline/verify-source.mts";
import { verifyWithInterfaces } from "../pipeline/module-interfaces.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { tsconfigOf } from "../tools/declaration-graph.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { linkFixtures } from "../pipeline/fixture-links.mts";
import { hostEnums } from "../tools/compiler-api.mts";
import { deferredIdentity } from "../tools/type-term.mts";
import { cases } from "../pipeline/cases.mts";
import type { Ast } from "../tools/fragment.mts";
import type { TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import { emptyEffect, ordinaryEffect } from "../tools/type-graph.mts";
import { forcedProposals, interfaceControls } from "./single-pass-control-inputs.mts";

process.env.TSCERT_ROUTE = "single-pass";
const root = resolve(import.meta.dirname, "..");
const isObject = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}

/** A finished operation a control ran, counted as an executed or a replayed
 * one (`tested`'s count); a replayed timeout or an unfinished one fails it. */
function counted(invoked: Invoked): Invoked {
  const { execution } = invoked.record;
  if (execution === "replayed") controlOperations.replayed++;
  else if (ranStage(invoked.record)) {
    controlOperations.executed++;
    controlOperations.elapsedMs += invoked.record.elapsedMs;
  } else throw Error(`control: ${invoked.record.stage} neither ran nor replayed a finished result (${execution})`);
  return invoked;
}

/** A unit's verdict from the pass: accepted, and closed when it and every
 * unit it depends on are accepted (a module unit only where its line is
 * printed), as the route reads it. */
type Verdict = { accepted: boolean; closed: boolean; refusal: string };
/** The pass over `fragment` under `force` (none for an unforced run). */
type Pass = { status: number | null; stdout: string; stderr: string; verdicts: Map<string, Verdict> };
function pass(fragment: string, force: readonly string[] = [], names: string = ""): Pass {
  const work = runDirectory("single-pass-control-");
  const given = join(work, "given.jsonl"), standins = join(work, "standins.json");
  writeFileSync(given, "");
  writeFileSync(standins, '{"functions":[],"imports":[]}');
  const ast: unknown = JSON.parse(readFileSync(fragment, "utf8"));
  const key = isObject(ast) && typeof ast.file === "string" ? ast.file : "";
  const { run, interfaces } = verifyWithInterfaces(fragment, key, names, standins, { mode: 8, fuel: 12, rounds: 4096,
    force, allCuts: false, given, work: join(work, "interfaces"),
    invocation: { limitMs: 60_000, force: false, recorder: null } });
  for (const r of interfaces.records) counted(r);
  counted(run);
  const verdicts = new Map<string, Verdict>();
  const depends = new Map<string, string[]>();
  for (const line of run.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const value: unknown = JSON.parse(line);
    if (!isObject(value) || typeof value.unit !== "string") continue;
    const accepted = value.accepted === true;
    verdicts.set(value.unit, { accepted, closed: accepted, refusal: typeof value.refusal === "string" ? value.refusal : "" });
    depends.set(value.unit, Array.isArray(value.depends) ? value.depends.filter((d) => typeof d === "string") : []);
  }
  for (let changed = true; changed; ) {
    changed = false;
    for (const [unit, v] of verdicts) {
      if (v.closed && (depends.get(unit) ?? []).some((d) => verdicts.get(d)?.closed === false ||
          (d.startsWith("module:") && !verdicts.has(d)))) {
        v.closed = false;
        changed = true;
      }
    }
  }
  return { status: run.status, stdout: run.stdout, stderr: run.stderr, verdicts };
}
/** The pass's words: its refusal (standard error) and its verdicts. */
const words = (p: Pass): string => p.stderr + p.stdout;
/** Require `unit` accepted with every unit it depends on. */
function accepted(p: Pass, unit: string, what: string): void {
  assert.equal(p.verdicts.get(unit)?.closed, true, `${what}: ${unit} not accepted: ${words(p).slice(0, 2000)}`);
}
/** Require `unit` refused: its own refusal, or a unit it depends on
 * refused; or the file refused before any unit's verdict (the front).
 * `at` the refusal's text where the control states it. */
function refused(p: Pass, unit: string, what: string, at?: RegExp): void {
  const v = p.verdicts.get(unit);
  assert.ok(v === undefined ? p.status !== 0 : !v.closed, `${what}: ${unit} accepted: ${words(p).slice(0, 2000)}`);
  const text = v === undefined || v.refusal === "" ? words(p) : v.refusal;
  if (at !== undefined) assert.match(text, at, `${what}: refused otherwise: ${text.slice(0, 1500)}`);
}
/** Require the file refused: a unit refused, or the front. */
function refusedFile(p: Pass, what: string, at?: RegExp): void {
  assert.ok(p.status !== 0 || [...p.verdicts.values()].some((v) => !v.closed), `${what}: accepted: ${words(p).slice(0, 2000)}`);
  if (at !== undefined) assert.match(words(p), at, `${what}: refused otherwise: ${words(p).slice(0, 1500)}`);
}

/** A case checked on the single-pass route, its artifacts retained: one
 * run per case in a control process, its own to write beside. */
const caseRuns = new Map<string, string>();
function run(file: string): string {
  const held = caseRuns.get(file);
  if (held !== undefined) return held;
  const test = must(cases.find((c) => c.file === file), `case ${file}`);
  const outcome = checkSource(join(root, "pipeline/examples", `${file}.ts`),
    test.project ? tsconfigOf(resolve(root, test.project)) : undefined, test.typescriptErrors, undefined, true);
  assert.notEqual(outcome.status, "error", `${file}: ${outcome.status === "verified" ? "" : outcome.detail}`);
  caseRuns.set(file, outcome.artifacts);
  return outcome.artifacts;
}
const fragmentOf = (artifacts: string): string => join(artifacts, "fragment.json");
/** Write a forged parser document beside a run's artifacts. */
function forged(artifacts: string, name: string, document: Ast | Record<string, unknown>): string {
  const path = join(artifacts, `${name}.json`);
  writeFileSync(path, JSON.stringify(document) ?? "");
  return path;
}

const controls: { name: string; body: () => Promise<void> }[] = [];
const control = (name: string, body: () => Promise<void>): void => {
  controls.push({ name, body });
};
/** Controls the route accepts where the old route refused the same forged
 * input: kept as written, run only with TSCERT_SINGLE_PASS_STOPS=1, listed
 * by every run, until the route refuses them or they are decided. */
const stops = new Set<number>();
const stop = (name: string, body: () => Promise<void>): void => {
  stops.add(controls.push({ name: `stop: ${name}`, body }) - 1);
};
const serving: boolean = process.argv[2] === "--controls";
const say = (line: string): void => {
  process.stdout.write(`${line}\n`);
};

// ---------------------------------------------------------------------------
// Forced proposals: the type computation states something false; the unit is
// then refused. A positive case's unit is accepted unforced.

for (const k of forcedProposals) {
  control(`forced ${k.force}: ${k.file} ${k.unit}`, async (): Promise<void> => {
    const fragment = fragmentOf(run(k.file));
    const unforced = pass(fragment);
    if (k.positive) accepted(unforced, k.unit, `${k.file} unforced`);
    else refused(unforced, k.unit, `${k.file} unforced`);
    refused(pass(fragment, k.force.split(",")), k.unit, `${k.file} forced ${k.force}`, k.at);
    say(`forced ${k.force}: ${k.file} ${k.unit} ${k.positive ? "accepted unforced, " : ""}refused forced`);
  });
}

// ---------------------------------------------------------------------------
// Module interfaces: the store boundary of the interface stages.

control("module interfaces: the store boundary", async (): Promise<void> => {
  const artifacts = run("certified-value-import");
  const given = join(artifacts, "control-given.jsonl");
  writeFileSync(given, "");
  interfaceControls(fragmentOf(artifacts), given, join(artifacts, "interface-controls"), say, counted);
});

// ---------------------------------------------------------------------------
// Forged fragments: the parser's document forged, refused by the pass. Each
// is a control of pipeline/test.mts's whose forgery the old route searched
// and checked, run through the pass.

/** A case's fragment, parsed. */
const fragmentAst = (artifacts: string): Ast => readFragmentFile(fragmentOf(artifacts));
/** The unit of the function `name` of a fragment: `name@<its name's position>`. */
function unitOf(ast: Ast, name: string): string {
  const fn = must(ast.functions.find((f) => f.name === name), `function ${name}`);
  return `${name}@${fn.namePos[0]}`;
}
/** Visit every object of a parsed value, children first. */
function visitAll(value: unknown, at: (node: Record<string, unknown>) => void): void {
  if (Array.isArray(value)) { for (const child of value) visitAll(child, at); return; }
  if (!isObject(value)) return;
  for (const child of Object.values(value)) visitAll(child, at);
  at(value);
}

/** Units of a control's case the route refuses unforced for want of a
 * loop-head fact (the 78 cases of the single-pass route that need given
 * loop-head facts): a forged refusal there shows nothing until the unit
 * verifies, so the control requires the unit refused unforced, and fails
 * once it is accepted, when its honest baseline is to be required. */
const lostBaselines: ReadonlySet<string> = new Set([
  "bounds-cell-invariant walk@143", "stated-slot-collect collect@696", "type-invariant-walker countBreaks@1414",
  "stated-region-steps scan@828", "bounds-quantified-invariant read@286",
]);
/** The honest baseline of a forged-fragment control: the case's `unit`
 * accepted unforced, or refused where `lostBaselines` lists it. */
function honest(file: string, unit: string, p: Pass = pass(fragmentOf(run(file)))): void {
  if (!lostBaselines.has(`${file} ${unit}`)) {
    accepted(p, unit, `${file} honest`);
    return;
  }
  assert.notEqual(p.verdicts.get(unit)?.closed, true,
    `${file} ${unit}: accepted unforced: require its honest baseline (remove it from lostBaselines)`);
  say(`${file} ${unit}: honest baseline refused on the route (no loop-head fact); the forged refusal shows nothing until it verifies`);
}

control("forged fragment: a false bound in a Boolean postcondition", async (): Promise<void> => {
  const artifacts = run("pretext-clause-postcondition");
  const ast = fragmentAst(artifacts);
  const unit = unitOf(ast, "advance");
  honest("pretext-clause-postcondition", unit);
  must(ast.functions.find((f) => f.name === "advance"), "advance").ensures.push({ guarded: { slot: 0, path: [], tag: "false",
    body: { linear: { fact: { le: { form: [[{ kind: "value", slot: 3, path: ["index"] }, 1]], bound: -1 } } } } } });
  refused(pass(forged(artifacts, "forged-boolean-postcondition", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("Boolean postconditions: a false bound under a true return is refused at the return");
});

control("forged fragment: a quantified precondition removed", async (): Promise<void> => {
  const artifacts = run("bounds-quantified-invariant");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "read"), "read's contract");
  assert.ok(fn.requires.some((f) => "every" in f));
  honest("bounds-quantified-invariant", unitOf(ast, "read"));
  fn.requires = [];
  refused(pass(forged(artifacts, "without-quantified-precondition", ast)), unitOf(ast, "read"), "forged");
  say("bounds: the fragment without its quantified precondition refused");
});

control("forged fragment: a false loop-cell invariant", async (): Promise<void> => {
  const artifacts = run("bounds-cell-invariant");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "walk"), "walk's body");
  const unit = unitOf(ast, "walk");
  honest("bounds-cell-invariant", unit);
  visitAll(fn.body, (value) => {
    if (value.k === "while" && isObject(value.invariant) && Array.isArray(value.invariant.facts))
      value.invariant.facts.push({ linear: { fact: { le: { form: [], bound: -1 } } } });
  });
  refused(pass(forged(artifacts, "false-cell-invariant", ast)), unit, "forged");
  say("bounds: a false cell invariant written into the loop refused");
});

control("forged fragment: a closure's written precondition removed", async (): Promise<void> => {
  const artifacts = run("closure-precondition");
  const ast = fragmentAst(artifacts);
  const unforced = pass(fragmentOf(artifacts));
  visitAll(ast, (value) => {
    if (value.k === "lambda") value.requires = [];
  });
  const p = pass(forged(artifacts, "closure-without-precondition", ast));
  const lost = [...unforced.verdicts].filter(([u, v]) => v.closed && p.verdicts.get(u)?.closed !== true).map(([u]) => u);
  assert.ok(lost.length > 0 || p.status !== 0 && p.verdicts.size === 0, `forged: no unit refused: ${words(p).slice(0, 2000)}`);
  say(`closures: the fragment without the closure's written precondition refused (${lost.join(", ") || "the front"})`);
});

/** A function's statement forged in the fragment: `stated` replaced. */
type Stated = NonNullable<Ast["functions"][number]["stated"]>;
function forgedStatement(artifacts: string, name: string, document: string, stated: Stated,
    expected?: Stated["regions"]): Pass {
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === name), name);
  if (expected === undefined) assert.equal(fn.stated, null, `${name} states nothing`);
  else assert.deepEqual(fn.stated?.regions, expected, `${name}'s regions`);
  fn.stated = stated;
  return pass(forged(artifacts, document, ast));
}

control("forged fragment: a fresh result stated of an identity function", async (): Promise<void> => {
  const artifacts = run("stated-fresh");
  const unit = unitOf(fragmentAst(artifacts), "same");
  honest("stated-fresh", unit);
  refused(forgedStatement(artifacts, "same", "forged-fresh-fragment",
    { footprint: { value: "any", store: "any" }, onThrow: false, fresh: true, regions: [] }), unit, "forged");
  say("forged fresh result: an identity function's statement forged to promise a fresh result, refused at its unit");
});

control("forged fragment: store regions moved", async (): Promise<void> => {
  const artifacts = run("stated-argument-store");
  const ast = fragmentAst(artifacts);
  const trim = unitOf(ast, "trim"), shrink = unitOf(ast, "shrink");
  const unforced = pass(fragmentOf(artifacts));
  honest("stated-argument-store", trim, unforced);
  honest("stated-argument-store", shrink, unforced);
  refused(forgedStatement(artifacts, "trim", "forged-region-fragment",
    { footprint: { value: "any", store: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path: [] }] },
    [{ position: 2, path: [] }]), trim, "trim's region at n");
  const ownAst = fragmentAst(artifacts);
  must(ownAst.functions.find((f) => f.name === "shrink"), "shrink").stated =
    { footprint: { value: "any", store: "keep" }, onThrow: false, fresh: false, regions: [{ position: 0, path: [] }] };
  refused(pass(forged(artifacts, "forged-receiver-region-fragment", ownAst)), shrink, "shrink's region at the receiver");
  say("forged store regions: a region moved to another parameter, and one at an undeclared receiver, each refused at its unit");
});

control("forged fragment: path regions moved", async (): Promise<void> => {
  const artifacts = run("stated-argument-path");
  const unit = unitOf(fragmentAst(artifacts), "readRuns");
  honest("stated-argument-path", unit);
  const moved: { document: string; path: string[] }[] = [{ document: "forged-path-region-fragment", path: [] },
    { document: "forged-path-field-fragment", path: ["closed"] }];
  for (const { document, path } of moved)
    refused(forgedStatement(artifacts, "readRuns", document,
      { footprint: { value: "any", store: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path }] },
      [{ position: 1, path: ["openBrackets"] }]), unit, document);
  say("forged path regions: a path region moved to its record's own store, and one through a field the type does not state, refused at the unit");
});

control("forged fragment: rebased regions", async (): Promise<void> => {
  const steps = run("stated-region-steps");
  const scan = unitOf(fragmentAst(steps), "scan");
  honest("stated-region-steps", scan);
  refused(forgedStatement(steps, "scan", "forged-rebased-fragment",
    { footprint: { value: "any", store: "keep" }, onThrow: false, fresh: false, regions: [{ position: 1, path: [] }] },
    [{ position: 1, path: ["open"] }]), scan, "scan's region at its record");
  const nullable = run("stated-region-nullable-write");
  const mark = unitOf(fragmentAst(nullable), "mark");
  honest("stated-region-nullable-write", mark);
  refused(forgedStatement(nullable, "mark", "forged-witness-fragment",
    { footprint: { value: "any", store: "keep" }, onThrow: false, fresh: false, regions: [{ position: 2, path: ["open"] }] },
    [{ position: 1, path: ["open"] }]), mark, "mark's region through a number");
  say("forged rebasing: a caller's region moved from the field's array to its record, and a region through a number parameter, each refused at its unit");
});

control("forged fragment: a fresh result whose store a caller pops", async (): Promise<void> => {
  const artifacts = run("invalid-stated-region-fresh-call");
  const unit = unitOf(fragmentAst(artifacts), "same");
  honest("invalid-stated-region-fresh-call", unit);
  refused(forgedStatement(artifacts, "same", "forged-fresh-call-fragment",
    { footprint: { value: "any", store: "any" }, onThrow: false, fresh: true, regions: [] }), unit, "forged");
  say("forged fresh store: a fresh result forged onto a function returning its parameter refused at the function's unit");
});

control("forged fragment: an old array at a slot's join", async (): Promise<void> => {
  const artifacts = run("stated-slot-collect");
  const ast = fragmentAst(artifacts);
  const unit = unitOf(ast, "collect");
  honest("stated-slot-collect", unit);
  let replaced = 0;
  visitAll(ast, (node) => {
    const rhs = node.rhs;
    if (node.k === "nullishAssign" && node.name === "acc" && isObject(rhs) && rhs.k === "arrayLit") {
      replaced++;
      node.rhs = { k: "id", pos: rhs.pos, name: "xs" };
    }
  });
  assert.equal(replaced, 1, "one `acc ??= []`");
  refused(pass(forged(artifacts, "forged-slot-join-fragment", ast)), unit, "forged");
  say("forged slot join: an old array on the nullish path of `acc ??= …`, refused at its unit");
});

control("forged fragment: a false postcondition", async (): Promise<void> => {
  const artifacts = run("type-invariant-walker");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "countBreaks"), "countBreaks");
  const unit = unitOf(ast, "countBreaks");
  honest("type-invariant-walker", unit);
  assert.ok(fn.ensures.every((f) => !JSON.stringify(f).includes('"slot":0')), "countBreaks states no result fact");
  fn.ensures = [...fn.ensures, { int: { slot: 0 } },
    { linear: { fact: { le: { form: [[{ kind: "value", slot: 0, path: [] }, 1]], bound: -1 } } } }];
  refused(pass(forged(artifacts, "forged-ensures-fragment", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("type invariants: a postcondition forged into the document, refused at the return");
});

control("forged fragment: a false parameter fact at the returns", async (): Promise<void> => {
  const artifacts = run("cursor-invariant-after-writing-call");
  const ast = fragmentAst(artifacts);
  const fn = must(ast.functions.find((f) => f.name === "step"), "step");
  const unit = unitOf(ast, "step");
  honest("cursor-invariant-after-writing-call", unit);
  fn.ensures = [...fn.ensures,
    { linear: { fact: { le: { form: [[{ kind: "value", slot: 3, path: ["segmentIndex"] }, 1]], bound: -1 } } } }];
  refused(pass(forged(artifacts, "forged-parameter-ensures-fragment", ast)), unit, "forged", /return at node \d+: the postcondition/);
  say("type invariants: a parameter's fact at the returns forged into the document, refused at a return");
});

control("omitted units: escapes in omitted code", async (): Promise<void> => {
  for (const file of ["invalid-module-cache-omitted-default", "invalid-module-cache-omitted-let"]) {
    using outcome = checkSource(join(root, "pipeline/examples", `${file}.ts`), undefined, false, undefined, true,
      { omitted: ["leak"], select: null });
    assert.ok(outcome.status === "unverified" || outcome.status === "unsupported", `${file}: ${outcome.status}`);
    assert.match(outcome.detail, /write/, `${file}: ${outcome.detail.slice(0, 600)}`);
  }
  say("module cache: escapes in omitted code keep the cache's write refused");
});

const enumMembers = new Map<string, string>([["SyntaxKind", "Identifier"], ["NodeFlags", "Const"], ["TypeFlags", "Union"],
  ["SymbolFlags", "Alias"], ["SignatureKind", "Call"], ["ElementFlags", "Required"], ["DiagnosticCategory", "Error"],
  ["TypePredicateKind", "Identifier"]]);
for (const reexport of [false, true]) for (const mismatched of [false, true])
  control(`compiler enum binding, ${reexport ? "re-exported" : "direct"}, ${mismatched ? "mismatched" : "audited"}`, async (): Promise<void> => {
    const audited = resolve(root, "tools/node_modules/typescript");
    const dir = runDirectory("tscert-compiler-enum-binding-");
    const installed = join(dir, "node_modules", "typescript");
    mkdirSync(join(dir, "node_modules"));
    const member = (name: string): string => must(enumMembers.get(name), `a member of ${name}`);
    if (mismatched) {
      mkdirSync(installed);
      writeFileSync(join(installed, "package.json"), JSON.stringify({ name: "typescript", type: "module",
        exports: { "./unstable/ast": "./enums.js", "./unstable/sync": "./enums.js" } }));
      writeFileSync(join(installed, "enums.js"), hostEnums.map(({ name }) =>
        `export const ${name} = { ${member(name)}: -123 };`).join("\n"));
    } else symlinkSync(audited, installed);
    writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
      module: "preserve", moduleResolution: "bundler", target: "es2022", lib: ["es2022"], types: [],
      allowImportingTsExtensions: true, paths: {
        "typescript/unstable/ast": [join(audited, "dist/ast/index.d.ts")],
        "typescript/unstable/sync": [join(audited, "dist/api/sync/api.d.ts")],
      } }, include: ["*.ts"] }));
    for (const { name } of hostEnums) {
      const entry = name === "SyntaxKind" || name === "NodeFlags" ? "ast" : "sync";
      writeFileSync(join(dir, "barrel.ts"), `export { ${name} as Enum } from "typescript/unstable/${entry}";\n`);
      const file = join(dir, "value.ts");
      writeFileSync(file, `import { ${reexport ? "Enum" : name + " as Enum"} } from "${reexport ? "./barrel.ts" : "typescript/unstable/" + entry}";\nexport function value(): Enum.${member(name)} { return Enum.${member(name)}; }\n`);
      using outcome = checkSource(file, tsconfigOf(dir), false, undefined, true);
      assert.equal(outcome.status, mismatched ? "unsupported" : "verified", `${name}, reexport=${reexport}: ${JSON.stringify(outcome)}`);
      if (outcome.status !== "verified") {
        assert.match(outcome.detail, /the host enum/);
        const ran = spawnSync(process.execPath, ["--input-type=module", "-e",
          `import { value } from ${JSON.stringify(pathToFileURL(file).href)}; console.log(value());`], { encoding: "utf8", cwd: dir });
        assert.equal(ran.status, 0, ran.stderr);
        assert.equal(ran.stdout.trim(), "-123", `${name}: Node returns the other installation's value`);
      }
    }
    say(`compiler enum binding, ${reexport ? "re-exported" : "direct"}: all ${hostEnums.length} enums, ${mismatched ? "mismatched bindings refused and counterexamples executed under Node" : "audited bindings verified"}`);
  });

control("forged fragment: malformed bodies", async (): Promise<void> => {
  const good = run("stateful-source/arithmetic");
  const source = fragmentAst(good);
  const fn = must(source.functions[0], "a function");
  const undef = { k: "lit", pos: [1, 3], lit: { a: "undefined" } };
  const effect = (e: object): object => ({ k: "effect", pos: [1, 3], e });
  const malformed: [unknown[], RegExp][] = [
    [[effect({ k: "unary", pos: [1, 3], op: "invalid", e: undef }), ...fn.body], /unknown unary operator 'invalid'/],
    [[effect({ k: "typeofTest", pos: [1, 3], shape: "invalid", equal: true, e: undef }), ...fn.body],
      /unsupported typeof test 'invalid'/],
    [[effect({ k: "futureExpression", pos: [1, 3], e: undef }), ...fn.body],
      /unsupported source expression at \[1,3\): expression outside the stateful fragment/],
    [[{ k: "break", pos: [1, 3], label: null }], /break or continue outside a source loop/],
  ];
  for (const [i, [body, refusal]] of malformed.entries())
    refusedFile(pass(forged(good, `planning-boundaries-${i}`, { ...source, functions: [{ ...fn, body }] })), `malformed ${i}`, refusal);
  say("malformed bodies: an unknown operator, typeof shape, expression kind and a break without a target, each refused by its own refusal");
});

control("forged fragment: a deferred mapped type", async (): Promise<void> => {
  const good = run("mapped-identity-named");
  const source = fragmentAst(good);
  const viewed = source.functions.find((f) => f.name === "viewed");
  const [param] = viewed?.params ?? [];
  assert.ok(viewed && param && param.type.k === "reference", "viewed takes a Shape");
  const deferred = deferredIdentity({ object: param.type, homomorphic: true, readonlyMod: "add", optionalMod: "keep", exact: null },
    { k: "atom", name: "never", span: param.type.span }, param.type.span);
  const atParameter = { ...source, functions: source.functions.map((f) => f !== viewed ? f
    : { ...f, params: [{ ...param, type: deferred }] }) };
  const atDefinition = { ...source, declarations: { ...source.declarations,
    definitions: source.declarations.definitions.map((d) => d.declaration.name === "Copy" ? { ...d, expression: deferred } : d) } };
  for (const [name, document] of [["parameter", atParameter], ["definition", atDefinition]] as const)
    refusedFile(pass(forged(good, `deferred-identity-${name}`, document)), name, /reference has no declaration equation/);
  say("a deferred mapped type in a forged parser document, at a parameter and at a definition: refused");
});

control("forged fragment: graph labels, claim-shaped annotations, unexamined fields", async (): Promise<void> => {
  const good = run("values");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(good), "utf8"));
  assert.ok(isObject(fragment));
  for (const [i, [retType, refusal]] of ([
    [{ a: "graph", label: 4 }, /source cannot state an internal graph label/],
    [{ top: false, atoms: [{ a: "boolean" }] }, /a source annotation is a type term, not a claim/],
  ] as const).entries()) {
    const document = structuredClone(fragment);
    assert.ok(Array.isArray(document.functions) && isObject(document.functions[0]) && "retType" in document.functions[0]);
    Object.assign(document.functions[0], { retType });
    refusedFile(pass(forged(good, `raw-graph-annotation-${i}`, document)), `retType ${i}`, refusal);
  }
  refusedFile(pass(forged(good, "extra-ast-field", { ...fragment, unexamined: true })), "root field", /unexpected fields/);
  for (const kind of ["id", "return"]) {
    const nested = structuredClone(fragment);
    const mark = (node: unknown): boolean => {
      if (Array.isArray(node)) return node.some(mark);
      if (!isObject(node)) return false;
      if (node.k === kind) {
        Object.assign(node, { unexamined: true });
        return true;
      }
      return Object.values(node).some(mark);
    };
    assert.ok(mark(nested), kind);
    refusedFile(pass(forged(good, `extra-${kind}-field`, nested)), `${kind} field`, /unexpected fields/);
  }
  say("a graph label, a claim-shaped annotation and an unexamined field in the parser's document, at its root or on a node: refused");
});

control("forged fragment: overload units at another function's code", async (): Promise<void> => {
  const artifacts = run("overloaded-function");
  const ast = fragmentAst(artifacts);
  const units = ast.functions.filter((f) => f.name === "pick");
  assert.equal(units.length, 2, "pick's overload units");
  must(units[1], "pick's second unit").body = must(ast.functions.find((f) => f.name === "count"), "count").body;
  refusedFile(pass(forged(artifacts, "forged-overload-code", ast)), "forged", /the units of pick are no overloads of one declaration's code/);
  say("overload units forged at another function's code: refused");
});

stop("forged fragment: a module function reading a function its document leaves out", async (): Promise<void> => {
  // The old route's producer refuses the module run (`unsupported: unbound
  // name describe at …`); the route accepts every unit: the importer's
  // check at the module's ordinary contracts reads no module body.
  const certified = run("certified-value-import");
  const ast = fragmentAst(certified);
  const module = must(ast.modules.find((m) => m.location.endsWith("certified.ts")), "certified.ts's module");
  assert.ok(module.functions.some((f) => f.name === "describe"), "`label` reads `describe`");
  module.functions = module.functions.filter((f) => f.name !== "describe");
  refusedFile(pass(forged(certified, "forged-absent-callee", ast)), "absent callee", /describe/);
  say("a module function reading a function its document leaves out: refused");
});

control("forged fragment: unbound names", async (): Promise<void> => {
  // A read renamed to a name nothing binds: a spread argument's operand and an assignment's target.
  // `located`: the refusal names a span holding the identifier; else (the
  // front's refusal of an assignment, which states no span) it names it.
  const unboundAt = (file: string, marker: string, skip: number, k: string, name: string, located: boolean): void => {
    const artifacts = run(file);
    const text = readFileSync(join(root, "pipeline/examples", `${file}.ts`), "utf8");
    const at = text.indexOf(marker) + skip;
    const document: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
    let renamed = 0;
    visitAll(document, (node) => {
      const pos = k === "assign" ? node.namePos : node.pos;
      if (node.k === k && node.name === name && Array.isArray(pos) && pos[0] === at) {
        renamed++;
        node.name = "missing";
      }
    });
    assert.equal(renamed, 1, `${file}: one ${k} node naming ${name} at ${at}`);
    assert.ok(isObject(document));
    const p = pass(forged(artifacts, `forged-unbound-${k}`, document));
    refusedFile(p, `${file} ${k}`);
    // Refused at a span holding the identifier.
    const spans = [...words(p).matchAll(/at \[(\d+),(\d+)\)/g)].map((m) => [Number(m[1]), Number(m[2])]);
    if (located) assert.ok(spans.some(([a, b]) => a <= at && at < b), `${file} ${k}: no refusal located at ${at}: ${words(p).slice(0, 1500)}`);
    else assert.match(words(p), /'missing'/, `${file} ${k}`);
  };
  unboundAt("array-readable", "...source", "...".length, "id", "source", true);
  unboundAt("assignment-effects", "(state = 1)", "(".length, "assign", "state", false);
  say("a read of a name its document does not bind, a spread operand's and an assignment target's: refused at a span holding it");
});

control("forged fragment: binder roles, an unguarded alias, written applications", async (): Promise<void> => {
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
  const forgeDocument = (file: string, name: string, change: (fragment: Ast) => void): Pass => {
    const artifacts = run(file);
    const fragment = fragmentAst(artifacts);
    change(fragment);
    return pass(forged(artifacts, name, fragment));
  };
  const forgeDefinition = (file: string, definition: string, name: string, change: (d: TypeDefinition) => void): Pass =>
    forgeDocument(file, name, (fragment) =>
      change(must(fragment.declarations.definitions.find((d) => d.declaration.name === definition), definition)));
  const withRun = (inner: TypeTerm) => (d: TypeDefinition): void => {
    assert(d.expression?.k === "object");
    must(d.expression.fields[0], "Runner's method").type = runner(inner);
  };
  const acceptedFile = (p: Pass, what: string): void =>
    assert.ok(p.status === 0 && [...p.verdicts.values()].every((v) => v.closed), `${what}: refused: ${words(p).slice(0, 1500)}`);
  acceptedFile(pass(fragmentOf(run("scheme-binder-roles"))), "scheme-binder-roles honest");
  acceptedFile(forgeDefinition("scheme-binder-roles", "Runner", "forged-shadowed-pack",
    withRun(scheme("P", method([binder("P")], null, binder("P"))))), "a nested binder shadowing the pack");
  refusedFile(forgeDefinition("scheme-binder-roles", "Runner", "forged-mixed-pack",
    withRun(scheme("Q", method([binder("Q"), binder("P")], null, binder("Q"))))), "a binder as value and pack",
    /Runner: generic contract at \[0,0\]: a binder used as both a value and an argument pack is not represented/);
  refusedFile(forgeDefinition("non-regular-alias", "Box", "forged-unguarded-alias", (d) => {
    assert(d.expression?.k === "object");
    const next = must(d.expression.fields.find((f) => f.name === "next"), "Box's next").type;
    assert(next.k === "union");
    d.expression = { k: "union", parts: [{ k: "parameter", index: 0, span }, must(next.parts[0], "Box<[T]>")], span };
  }), "unguarded alias",
  /unguarded alias cycle through Box: a recursive alias must reach itself through an object, array, tuple or function type/);
  const dependent = (fragment: Ast): Ast["declarations"]["applications"][number] =>
    must(fragment.declarations.applications.find((a) => a.site.endsWith("#dependent")), "dependent's B<U>");
  refusedFile(forgeDocument("written-scopes", "forged-written-argument", (fragment) => {
    dependent(fragment).args = [{ k: "atom", name: "number", span }];
  }), "a written argument", /a written application: the type argument for B's "T" .*does not establish its declared bound: number ≤ string/);
  refusedFile(forgeDocument("written-scopes", "forged-written-scope", (fragment) => {
    for (const level of dependent(fragment).scope) for (const b of level) b.bound = null;
  }), "a written scope", /a written application: the type argument for B's "T" .*does not establish its declared bound/);
  const relaxed = forgeDocument("invalid-computed-bound-typeof", "forged-written-bound", (fragment) => {
    const entry = must(fragment.declarations.applications.find((a) => a.reference.name === "BoxOf"), "BoxOf<number>");
    entry.bounds = entry.bounds.map(() => null);
  });
  // The bounds a written application is checked at are the document's
  // (the front end supplies every one): nulled, the application is accepted,
  // as the old route's search accepts it.
  acceptedFile(relaxed, "the written bounds nulled");
  for (const [name, argument] of [["number", { k: "atom", name: "number", span }],
      ["callable", { k: "callable", span }]] as const)
    refusedFile(forgeDocument("blocker-returntype-typeof", `forged-returntype-${name}`, (fragment) => {
      must(fragment.declarations.applications.find((a) => a.reference.name === "ReturnType"), "ReturnType<typeof find>").args = [argument];
    }), `ReturnType at ${name}`, /the type argument for ReturnType's "T" .*does not establish its declared bound/);
  for (const [alias, argument] of [["Parameters", { k: "atom", name: "class", span }],
      ["ConstructorParameters", { k: "atom", name: "function", span }]] as const)
    refusedFile(forgeDocument("parameters-typeof", `forged-${alias}`, (fragment) => {
      must(fragment.declarations.applications.find((a) => a.reference.name === alias), alias).args = [argument];
    }), alias, new RegExp(`the type argument for ${alias}'s "T" .*does not establish its declared bound`));
  refusedFile(forgeDocument("written-dependent-default", "forged-short-reference", (fragment) => {
    let found = 0;
    visitAll(fragment.functions, (value) => {
      if (value.k === "reference" && Array.isArray(value.args) && (JSON.stringify(value.reference) ?? "").includes('"name":"Keys"')) {
        value.args.pop();
        found++;
      }
    });
    assert.ok(found, "a reference to Keys");
  }), "a short reference", /Keys applied to 1 type arguments of 2/);
  using exhausted = checkSource(join(root, "pipeline/examples/written-recursive-bound.ts"), undefined, false, 0, true);
  // Refused at the application, exhausted. (The route reports the front's
  // refusal as unsupported, where the old route's status is `exhausted`.)
  assert.ok(exhausted.status !== "verified" && exhausted.status !== "error", JSON.stringify(exhausted));
  assert.match("detail" in exhausted ? exhausted.detail : "", /source direct obligation at \[202,212\): subtype search exhausted/);
  say("binder roles, an unguarded alias, written arguments, scopes and references forged: each refused; a written obligation out of rounds exhausted");
});

control("forged declarations: the Promise tag", async (): Promise<void> => {
  // `Symbol.toStringTag` is the native `Promise` contract's: the declaration
  // document lists it by its identity, only that contract's prototype holds
  // it, its `then` names no `PromiseLike`, and no object the source makes is
  // keyed by it. A document tampered with in any of these is refused where
  // evidence is produced and where it is checked.
  const tagged = (good: string, name: string, edit: (ast: Ast) => string, refusal: RegExp): void => {
    const path = join(good, `${name}.fragment.json`);
    writeFileSync(path, edit(readFragmentFile(fragmentOf(good))));
    refusedFile(pass(path), name, refusal);
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
      receiverStore: false, onThrow: false, receiverOwn: false, freshObject: false, requires: null, elements: null,
      pre: [], ensures: [], receiverGrows: false, elementWrite: null },
      receiver: null, params: [], rest: null,
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
    writeFileSync(exact, fakeAt(readFragmentFile(fragmentOf(inherited)), "exact"));
    const produced = pass(exact);
    assert.ok(produced.status === 0 && [...produced.verdicts.values()].every((v) => v.closed), words(produced).slice(0, 1500));
  }
  // Refused at the read of `f` in `return f` (the old route: `source
  // expression obligation at [at,at+1)`; the route names the node).
  tagged(inherited, "tag-fake-untagged", ast => fakeAt(ast, "untagged"), /expression at node \d+: Verification\.Tm\.var 0 /);
  assert.ok(at > 0);
  const otherPrototype = /a prototype holding `Symbol.toStringTag` other than the native Promise's/;
  tagged(inherited, "tag-fake-tagged", ast => fakeAt(ast, "distinct"), otherPrototype);
  tagged(inherited, "tag-fake-base", ast => fakeAt(ast, "base"), otherPrototype);
  tagged(inherited, "tag-fake-callable", ast => fakeAt(ast, "callable"), /a prototype is stated as no record/);
  say("forged tag documents: the tag renamed, dropped, stated of another prototype or a base's, PromiseLike in the native then, an allocation keyed by the tag; a contract with the native methods and no tag, a callable prototype: refused");
});

control("forged fragment: a reserved member name", async (): Promise<void> => {
  // The parser reserves `message` and `stack` as member names of a class
  // extending `Error`; the pass reads no class declaration: the fragment with
  // `text` renamed `stack` is accepted, the reservation the parser's alone.
  const methods = run("error-subclass-methods");
  const path = join(methods, "forged-stack-member-fragment.json");
  writeFileSync(path, readFileSync(fragmentOf(methods), "utf8").replaceAll('"text"', '"stack"').replaceAll("Located.text", "Located.stack"));
  assert.ok(readFileSync(path, "utf8").includes('"name":"stack"'), "the forged fragment names a member `stack`");
  const p = pass(path);
  assert.ok(p.status === 0 && [...p.verdicts.values()].every((v) => v.closed), words(p).slice(0, 1500));
  say("forged stack member: accepted by the pass, the reservation enforced by the parser alone");
});

control("forged fragment: writes renamed to a reserved key", async (): Promise<void> => {
  const twin = run("reserved-write-twin");
  const source = readFileSync(sourceKey(twin), "utf8");
  for (const [key, write] of [["stackPattern", "o.stackPattern"], ["stackUpdate", 'o.stackUpdate += "s"'],
      ["stackLogical", 'o.stackLogical ??= "s"'], ["stackCallback", "o.stackCallback = v"], ["stackComputed", 'o[k] = "s"']] as const) {
    const path = join(twin, `forged-${key}-fragment.json`);
    writeFileSync(path, readFileSync(fragmentOf(twin), "utf8").replaceAll(`"${key}"`, '"stack"'));
    const start = source.indexOf(write);
    const at = `source refusal at [${start},${start + write.length}): a write at a key that may be \`message\`, \`stack\` or \`cause\``;
    const p = pass(path);
    refusedFile(p, key);
    assert.ok(words(p).includes(at), `${key}: refused otherwise: ${words(p).slice(0, 1500)}`);
  }
  say("forged reserved writes: each write form renamed to `stack`, refused at the write");
});

control("forged declarations: a generic member's result", async (): Promise<void> => {
  // The class's declaration tampered to promise a number where the closure
  // returns its binder is refused at the construct code; the untampered one
  // is accepted. `make` alone is kept.
  const classGeneric = run("class-generic-method");
  const source = readFileSync(sourceKey(classGeneric), "utf8");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(classGeneric), "utf8"));
  assert.ok(isObject(fragment) && Array.isArray(fragment.functions));
  fragment.functions = fragment.functions.filter((f: unknown) => isObject(f) && f.name === "make");
  const kept = JSON.stringify(fragment);
  const at = source.indexOf("pick<V>(a: V): V") + "pick<V>(a: V): ".length;
  const declared = `"result":{"k":"binder","name":"V","span":[${at},${at + 1}]}`;
  assert.ok(kept.includes(declared), "pick's declared result");
  const search = (name: string, text: string): Pass => {
    const path = join(classGeneric, `${name}.json`);
    writeFileSync(path, text);
    return pass(path);
  };
  const derived = search("make-only", kept);
  assert.ok(derived.status === 0 && [...derived.verdicts.values()].every((v) => v.closed), words(derived).slice(0, 1500));
  const make = [...derived.verdicts.keys()].find((u) => u.startsWith("make@"));
  refused(search("forged-member-result", kept.replace(declared, '"result":{"k":"atom","name":"number","span":[0,0]}')),
    must(make, "make's unit"), "forged member result");
  say("forged declarations: a generic member's result narrowed in the class's declaration, refused at the construct code");
});

stop("forged declarations: another import closure", async (): Promise<void> => {
  // The fragment's own code over another file's declarations: other types.
  // The old route refuses the claims, which name declarations by position;
  // the route accepts every unit (values' `identity` reads no declaration).
  const good = run("values");
  const fragment: unknown = JSON.parse(readFileSync(fragmentOf(good), "utf8"));
  const json: unknown = JSON.parse(readFileSync(fragmentOf(run("collections-json-uninherited-key")), "utf8"));
  assert.ok(isObject(fragment) && isObject(json) && "declarations" in json);
  refusedFile(pass(forged(good, "forged-import", { ...fragment, declarations: json.declarations })), "forged import closure");
  say("forged import closure: refused");
});

control("forged declarations: unequal bound member effects", async (): Promise<void> => {
  // A method bound to a union of hosts needs each host's member at one
  // signature: one host's `next` given the empty effect.
  const artifacts = run("bind-union-host");
  const ast = fragmentAst(artifacts);
  honest("bind-union-host", "total@1704");
  const host = must(ast.declarations.definitions.find((d) => d.declaration.name === "Countdown"), "Countdown");
  assert.ok(host.expression?.k === "object");
  const next = must(host.expression.fields.find((f) => f.name === "next"), "Countdown.next");
  assert.ok(next.type.k === "function");
  assert.deepEqual(next.type.effect, ordinaryEffect);
  next.type.effect = emptyEffect;
  refused(pass(forged(artifacts, "unequal-bound-member-effects", ast)), "total@1704", "unequal member effects");
  say("unequal bound member effects: refused at the bound call's unit");
});

control("forged fragment: explicit type arguments widened", async (): Promise<void> => {
  // `reduce<number | null>` written as `reduce<number | null | string>`, and
  // `same<number | boolean>` as `same<number | boolean | string>`.
  for (const [file, kind] of [["closure-result-contract", "invoke"], ["explicit-type-arguments", "apply"]] as const) {
    const artifacts = run(file);
    const unforced = pass(fragmentOf(artifacts));
    const ast: unknown = JSON.parse(readFileSync(fragmentOf(artifacts), "utf8"));
    const calls: { parts: unknown[]; span: unknown }[][] = [];
    const found: { owner: string | null } = { owner: null };
    visitAll(ast, (node) => {
      if (node.k === kind && Array.isArray(node.typeArgs) && node.typeArgs.length > 0 && calls.length === 0)
        calls.push(node.typeArgs.filter((a): a is { parts: unknown[]; span: unknown } => isObject(a) && Array.isArray(a.parts)));
      if (calls.length > 0 && found.owner === null && typeof node.name === "string" && Array.isArray(node.namePos) &&
          typeof node.namePos[0] === "number" && "body" in node) found.owner = `${node.name}@${node.namePos[0]}`;
    });
    const [typeArg] = must(calls[0], "the call's type arguments");
    must(typeArg, "the type argument").parts.push({ k: "atom", name: "string", span: typeArg?.span });
    assert.ok(isObject(ast));
    const unit = must(found.owner, "the call's function");
    honest(file, unit, unforced);
    refused(pass(forged(artifacts, "forged-type-argument", ast)), unit, `${file} widened`);
  }
  say("explicit type arguments written wider than the call's instance: refused at the call's unit");
});

control("forged fragment: an array owning toJSON", async (): Promise<void> => {
  const artifacts = run("json-stringify-sparse");
  const ast = fragmentAst(artifacts);
  const nested = must(ast.functions.find((f) => f.name === "nested"), "nested's declaration");
  const unit = unitOf(ast, "nested");
  honest("json-stringify-sparse", unit);
  const rows = must(nested.params[0], "nested's parameter");
  const span = rows.type.span;
  rows.type = { k: "intersection", span, parts: [rows.type, { k: "object", span, stringIndex: null, calls: [],
    fields: [{ name: "toJSON", optional: false, readonly: false, span, type: { k: "function", effect: ordinaryEffect,
      receiver: null, params: [], rest: null, result: { k: "atom", name: "undefined", span }, span } }] }] };
  refused(pass(forged(artifacts, "forged-array-tojson", ast)), unit, "forged", /intersection is empty/);
  say("an array owning toJSON, forged past the parser: refused at the empty intersection");
});

control("forged fragment: a generic closure's statement", async (): Promise<void> => {
  const artifacts = run("generic-function-type-annotation");
  const fragment = readFileSync(fragmentOf(artifacts), "utf8");
  const lambda = fragment.search(/"k":"lambda","pos":\[\d+,\d+\],"typeParams":\[\{/);
  assert.ok(lambda >= 0, "a generic closure");
  const unstated = fragment.indexOf('"stated":null', lambda);
  assert.ok(unstated > lambda, "its statement");
  const path = join(artifacts, "forged-generic-stated-fragment.json");
  writeFileSync(path, fragment.slice(0, unstated) +
    '"stated":{"footprint":{"value":"keep","store":"keep"},"onThrow":false,"fresh":false,"regions":[]}' + fragment.slice(unstated + '"stated":null'.length));
  refusedFile(pass(path), "forged", /a generic closure states no effect/);
  say("stated generic closure: a statement written into the Fragment refused");
});

control("forged fragment: a method's statement dropped", async (): Promise<void> => {
  // The class's construction is checked against the member's statement:
  // with `bump`'s statement dropped, the class is still refused.
  const artifacts = run("invalid-method-effect-construction");
  const fragment = readFileSync(fragmentOf(artifacts), "utf8");
  const statement = '"stated":{"footprint":{"value":"keep","store":"keep"},"onThrow":false,"fresh":false,"regions":[]}';
  assert.equal(fragment.split(statement).length, 2, "bump's statement");
  const path = join(artifacts, "forged-unstated-fragment.json");
  writeFileSync(path, fragment.replace(statement, '"stated":null'));
  const unforced = pass(fragmentOf(artifacts));
  const p = pass(path);
  refusedFile(p, "forged");
  // Refused where the honest document is: the construction.
  for (const [u, v] of unforced.verdicts) if (!v.closed) refused(p, u, `forged: ${u}`);
  say("unstated method of a stated member: the class's construction refused, the Fragment's statement dropped");
});

control("stated import: the exporting module refused", async (): Promise<void> => {
  using importer = checkSource(join(root, "pipeline/examples/stated-assumed-value-import.ts"),
    tsconfigOf(join(root, "pipeline/imports-project")), false, undefined, true);
  const project = join(root, "pipeline/imports-project");
  using outcome = checkSource(join(project, "stated.ts"), tsconfigOf(project), false, undefined, true);
  assert.equal(importer.status, "verified", JSON.stringify(importer).slice(0, 1500));
  if (outcome.status === "verified") assert.fail("drain's module verified");
  const drain = must((outcome.units ?? []).find((u) => u.unit.startsWith("drain@")), "drain's unit");
  assert.notEqual(drain.status, "verified");
  assert.match(drain.detail, /footprint/);
  say("stated import: the importer verified relative to the import assumption, the exporting module's drain refused at its footprint");
});

// ---------------------------------------------------------------------------
// The pool.

type Operations = { executed: number; replayed: number; elapsedMs: number };
type Finished = { finished: number; error: string | null; operations: Operations; retiring: boolean };
const readFinished = (value: unknown): Finished => {
  if (!isObject(value) || typeof value.finished !== "number" || !(value.error === null || typeof value.error === "string") ||
      typeof value.retiring !== "boolean" || !isObject(value.operations))
    throw Error(`not a control's result: ${JSON.stringify(value)}`);
  const o = value.operations;
  if (typeof o.executed !== "number" || typeof o.replayed !== "number" || typeof o.elapsedMs !== "number")
    throw Error(`not a control's result: ${JSON.stringify(value)}`);
  return { finished: value.finished, error: value.error, retiring: value.retiring,
    operations: { executed: o.executed, replayed: o.replayed, elapsedMs: o.elapsedMs } };
};
const chosen = process.argv.slice(serving ? 3 : 2);
if (serving) {
  // A control process: one control per message. A process whose caches may
  // disagree with the file system reports its control and exits.
  process.on("message", (message: unknown) => {
    if (!isObject(message) || typeof message.control !== "number") throw Error(`not a control's request: ${JSON.stringify(message)}`);
    const index = message.control;
    const entry = controls[index];
    if (entry === undefined) throw Error(`no control ${index}`);
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
    entry.body().then(() => report(null), (error: unknown) =>
      report(error instanceof Error ? error.stack ?? error.message : String(error)));
  });
  process.on("disconnect", () => process.exit(0));
} else {
  // `node tests/single-pass-controls.mts [pattern…]`: the controls whose
  // names contain a pattern, every one with none.
  startEviction();
  linkFixtures();
  const started = performance.now();
  const failures: string[] = [];
  const tally: Operations = { executed: 0, replayed: 0, elapsedMs: 0 };
  const withStops = process.env.TSCERT_SINGLE_PASS_STOPS === "1";
  const pending = controls.flatMap((c, i) => (withStops || !stops.has(i)) &&
    (chosen.length === 0 || chosen.some((p) => c.name.includes(p))) ? [i] : []);
  if (!withStops)
    for (const i of stops) process.stdout.write(`not run (TSCERT_SINGLE_PASS_STOPS=1 runs it): ${controls[i]?.name}\n`);
  const total = pending.length;
  let processes = 0;
  const width = Math.max(1, Math.min(availableParallelism(), pending.length));
  const lane = (): Promise<void> => new Promise<void>((done, fail) => {
    processes++;
    const child = fork(import.meta.filename, ["--controls"], { stdio: ["ignore", "pipe", "pipe", "ipc"] });
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
      if (index !== undefined) child.send({ control: index });
      else child.disconnect();
    };
    child.on("message", (message: unknown) => {
      const result = readFinished(message);
      tally.executed += result.operations.executed;
      tally.replayed += result.operations.replayed;
      tally.elapsedMs += result.operations.elapsedMs;
      if (result.error !== null) failures.push(`${controls[result.finished]?.name ?? result.finished}: ${result.error}`);
      if (result.retiring) retired = true;
      else give();
    });
    child.on("error", fail);
    child.on("exit", (status: number | null) => {
      if (printed) process.stdout.write(printed + "\n");
      if (status !== 0) failures.push(`a control process exited with ${status}: ${errors}`);
      if (retired && status === 0 && pending.length > 0) lane().then(done, fail);
      else done();
    });
    give();
  });
  await Promise.all(Array.from({ length: width }, lane));
  process.stdout.write(`single-pass controls: ${total} in ${((performance.now() - started) / 1000).toFixed(1)} s on ${width} ` +
    `lanes (${processes} processes); their operations ${tally.executed} executed (${(tally.elapsedMs / 1000).toFixed(1)} s ` +
    `in all), ${tally.replayed} replayed\n`);
  assert.deepEqual(failures, [], failures.join("\n"));
}
