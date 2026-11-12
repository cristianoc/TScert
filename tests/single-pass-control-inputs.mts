// The single pass's controls' inputs, read by the suite of its controls
// (tests/single-pass-controls.mts) and by the agreement measure
// (dev/single-pass-agreement.mts) from this one list, so the two cannot
// drift: the forced proposals, and the store-boundary controls of the
// module-interface stages (dev/module-interface-controls.mts runs them alone).
import { chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import assert from "node:assert/strict";
import { prepareInterfaces } from "../pipeline/module-interfaces.mts";
import type { InterfaceOptions } from "../pipeline/module-interfaces.mts";
import { invokeProcess } from "../pipeline/stages.mts";
import type { Invoked } from "../pipeline/stages.mts";
import { verifierBuild, verifierCall } from "../pipeline/stage-execution.mts";
import type { Canonical } from "../pipeline/stage-execution.mts";

/** A forced proposal (`TSCERT_FORCE=<force>`): the pass's type computation
 * states something false at the case's unit. A positive one's unit is
 * accepted unforced, with every unit it depends on; every one's unit is
 * refused under its force, at the refusal `at` matches where it states one. */
export type ForcedProposal = { file: string; unit: string; force: string; positive?: boolean; at?: RegExp };
/** Forced proposals: unsafe programs remain refused; the positive declaration,
 * growth and copy cases are accepted unforced and refused at the false proposal. */
export const forcedProposals: readonly ForcedProposal[] = [
  { file: "stated-signatures-presence", unit: "signatures@605", force: "path-callees", positive: true },
  { file: "invalid-native-promise-invariant-result", unit: "widen@89", force: "instances", positive: true },
  { file: "early-let-literal", unit: "families@954", force: "early-contracts", positive: true },
  { file: "blocker-spread-tuple-field", unit: "returned@867", force: "objects", positive: true },
  { file: "blocker-prep-assign-error-value", unit: "absent@86", force: "copy-exclusions", positive: true },
  { file: "for-of-host-iterables", unit: "sum@631", force: "iteration-values", positive: true },
  { file: "optional-call-loop-cell", unit: "collect@300", force: "chains", positive: true },
  { file: "typed-array-float64", unit: "getKerning@474", force: "field-writes", positive: true },
  { file: "evolving-bindings", unit: "captured@736", force: "evolving", positive: true },
  { file: "array-first-use", unit: "tuple@268", force: "first-use", positive: true },
  { file: "object-growth", unit: "grow@191", force: "growth", positive: true },
  { file: "array-spread", unit: "spreadTuple@500", force: "copy-indexes", positive: true },
  { file: "invalid-method-effect-stated-throw-caught", unit: "wrong@596", force: "literals" },
  { file: "invalid-node-assert-catch-continue", unit: "rows@339", force: "literals" },
  { file: "invalid-cell-truthiness-narrowing", unit: "kept@176", force: "stale" },
  { file: "module-cache-keeps-lengths", unit: "count@478", force: "cells", positive: true },
  // (its early binding `cache` is also held at its written contract, `early-contracts`: forced with both)
  { file: "module-cache-before-initialization", unit: "rhs@341", force: "cells,early-contracts", positive: true },
  { file: "fresh-separation", unit: "handlerCell@1404", force: "cells", positive: true },
  { file: "module-cells-written-in-turn", unit: "aside@399", force: "cells", positive: true },
  { file: "early-bindings", unit: "count@471", force: "early", positive: true },
  { file: "invalid-exceptional-handler-fact", unit: "wrong@336", force: "throws" },
  { file: "invalid-object-spread-two-sources", unit: "count@156", force: "spreads" },
  { file: "invalid-keyed-read", unit: "pick@70", force: "keys" },
  { file: "invalid-declaration-pop-callback", unit: "dropped@359", force: "callees" },
  { file: "certified-value-import", unit: "tallies@829", force: "imports", positive: true },
  { file: "invalid-certified-write-value-import", unit: "zeros@319", force: "imports" },
  { file: "returned-closure-footprint", unit: "lazyRegExp@461", force: "results", positive: true },
  { file: "invalid-returned-closure-footprint", unit: "lastRead@421", force: "results" },
  { file: "invalid-compiler-api-guard-loop-partial", unit: "names@203", force: "guards" },
  { file: "invalid-read-narrows-write", unit: "wrong@187", force: "reads" },
  { file: "invalid-read-narrows-closure", unit: "wrong@153", force: "reads" },
  { file: "invalid-slot-path-call", unit: "keyText@477", force: "paths" },
  { file: "invalid-path-witness-alias", unit: "wrong@82", force: "paths" },
  { file: "invalid-closure-offer-narrower-mutation", unit: "wrong@275", force: "offers" },
  { file: "invalid-field-narrowing-for-of-callback", unit: "count@323", force: "loops" },
  { file: "invalid-field-narrowing-for-of-closure", unit: "count@343", force: "loops" },
  { file: "invalid-unassigned-let", unit: "readBeforeAssignment@113", force: "decided" },
  { file: "invalid-generic-closure-effect", unit: "stale@197", force: "schemes" },
  { file: "invalid-map-fresh-alias", unit: "drained@188", force: "callbacks" },
  { file: "invalid-map-fresh-reassigned", unit: "drained@156", force: "fresh" },
  { file: "invalid-closure-default-effect", unit: "stale@264", force: "defaults" },
  { file: "for-of-program-iterable", unit: "sum@2547", force: "binds", positive: true },
  { file: "bind-union-host", unit: "total@1704", force: "binds", positive: true },
  { file: "union-callee", unit: "renderEither@283", force: "arms", positive: true },
  { file: "invalid-compiler-api-guard-loop-finally", unit: "names@210", force: "finally" },
  { file: "invalid-closure-graph-captured-cell", unit: "counter@170", force: "never" },
  { file: "invalid-type-parameter-meet-narrowing", unit: "present@127", force: "meets" },
  { file: "invalid-negated-disjunction-saved", unit: "wrong@91", force: "implications" },
  { file: "invalid-closure-cell-capture-narrowed", unit: "wrong@181", force: "captures" },
  { file: "invalid-object-spread-width-replaced", unit: "wrong@385", force: "objects" },
  { file: "invalid-class-static-inherited-rest", unit: "rest@276", force: "spreads" },
  { file: "invalid-async-throw-only-arrow", unit: "wrong@347", force: "no-return" },
  { file: "invalid-async-throw-only-expression", unit: "wrong@361", force: "no-return" },
  { file: "invalid-async-throw-only-object-method", unit: "wrong@369", force: "no-return" },
  { file: "invalid-method-effect-throw-caught", unit: "wrong@487", force: "no-return" },
  { file: "map-stable-set", unit: "distinct@238", force: "steps", positive: true },
  { file: "loop-head-contents", unit: "continued@413", force: "head-entry", positive: true },
  { file: "returntype-guard", unit: "isName@125", force: "start-facts", positive: true },
  // An element read typed without its missing arm, refused at the read.
  { file: "native-length-literal", unit: "order@440", force: "elements", positive: true, at: /expression at node \d+: Verification\.Tm\.elemAt/ },
  // An array literal's spread of strings proposed at its number[] contract, refused at the literal
  // (no positive unit: the force skips a check that compatible operands pass).
  { file: "invalid-array-literal-spread", unit: "mixed@16", force: "array-spreads", at: /expression at node \d+: Verification\.Tm\.arrLit/ },
  { file: "invalid-dense-spread-element", unit: "wrong@16", force: "array-spreads", at: /expression at node \d+: Verification\.Tm\.arrLit/ },
];

function record(v: unknown): Record<string, unknown> {
  if (v === null || typeof v !== "object" || Array.isArray(v)) throw Error("expected object");
  return v as Record<string, unknown>; // asserted: checked non-null, non-array object
}
function list(v: unknown): unknown[] {
  if (!Array.isArray(v)) throw Error("expected array");
  return v;
}
function parsed(path: string): Record<string, unknown> {
  const v: unknown = JSON.parse(readFileSync(path, "utf8"));
  return record(v);
}
function manifestInput(v: Canonical): string {
  return JSON.stringify(v) ?? "";
}

/** The store-boundary controls of the module-interface stages over a
 * fragment with implementation imports and its given facts: a forged stored
 * interface is recomputed, an interface stale for an edited module is
 * refused, forced proposals and selected roots key apart, own-file and
 * reordered requests reach the same keys, an importer's forced execution
 * prints the same payload, and a timed-out or failed component publishes
 * nothing. Run over a fresh store of their own under `scratch`
 * (`TSCERT_STAGE_STORE`, restored after); each line they print is passed to
 * `log`; every operation they run is passed to `ran`. */
export function interfaceControls(fragment: string, given: string, scratch: string, log: (line: string) => void,
    ran: (invoked: Invoked) => void = () => {}): void {
  mkdirSync(scratch, { recursive: true });
  const work = mkdtempSync(join(scratch, "interface-controls-"));
  const previous = process.env.TSCERT_STAGE_STORE;
  const store = join(work, "store");
  process.env.TSCERT_STAGE_STORE = store;
  try {
    const prepare = (path: string, options: InterfaceOptions): ReturnType<typeof prepareInterfaces> => {
      const prepared = prepareInterfaces(path, options);
      for (const r of prepared.records) ran(r);
      return prepared;
    };
    const invoke = (...args: Parameters<typeof invokeProcess>): Invoked => {
      const invoked = invokeProcess(...args);
      ran(invoked);
      return invoked;
    };
    const options: InterfaceOptions = { mode: 8, fuel: 12, rounds: 4096, force: [], allCuts: false, given,
      work: join(work, "first"), invocation: { limitMs: 60_000, force: false, recorder: null } };
    const first = prepare(fragment, options);
    const original = readFileSync(first.path, "utf8");
    const warm = prepare(fragment, { ...options, work: join(work, "warm") });
    assert(warm.records.every((r) => r.record.execution === "replayed"));
    assert.equal(readFileSync(warm.path, "utf8"), original);
    const component = first.records.find((r) => r.record.stage === "module-interface");
    assert(component?.record.key);
    const stored = join(store, "entries", "module-interface", component.record.key, "stdout");
    chmodSync(stored, 0o644);
    writeFileSync(stored, '{"modules":[]}');
    const repaired = prepare(fragment, { ...options, work: join(work, "repaired") });
    assert(repaired.records.some((r) => r.record.stage === "module-interface" && r.record.execution === "executed"));
    assert.equal(readFileSync(repaired.path, "utf8"), original);
    log("forged stored interface: rejected by payload integrity, recomputed");

    const ast = parsed(fragment);
    const modules = list(ast.modules);
    assert(modules.length > 0);
    const module = record(modules[0]);
    module.sourceSha256 = "0".repeat(64);
    const edited = join(work, "edited.json");
    writeFileSync(edited, JSON.stringify(ast));
    const empty = join(work, "standins.json");
    writeFileSync(empty, '{"functions":[],"imports":[]}');
    assert.equal(typeof ast.file, "string");
    const stale = invoke(verifierCall(verifierBuild, ["--verify-interface-stage", "8", edited, first.path,
      given, empty, String(ast.file), "12", ""]), options.invocation);
    assert.equal(stale.status, 1);
    assert(stale.stderr.includes("stale interface:"));
    const changed = prepare(edited, { ...options, work: join(work, "changed") });
    assert(changed.records.some((r) => r.record.stage === "module-interface" && r.record.execution === "executed"));
    assert.notEqual(readFileSync(changed.path, "utf8"), original);
    log("module edited after publication: old interface refused; changed request misses");

    // Budgets, adversarial proposals and cuts are bound, while the importer
    // stage is reached only after every component has finished.
    const request = first.records.find((r) => r.record.stage === "module-interface");
    assert(request && manifestInput(request.record.manifest).includes("request.json"));
    const forced = prepare(fragment, { ...options, force: ["imports"], work: join(work, "forced") });
    assert(forced.records.filter((r) => r.record.stage === "module-interface").every((r) => r.record.execution === "executed"));
    assert.notDeepEqual(forced.records.map((r) => r.record.key), first.records.map((r) => r.record.key));
    log("forced proposals: separate component keys");

    // A normalized own-file run reaches the same complete component request.
    const source = parsed(fragment);
    const own = record(list(source.modules)[0]);
    assert.deepEqual(own.absent, []);
    const ownAst = { file: own.location, sourceSha256: own.sourceSha256, declarations: own.declarations,
      init: own.init, functions: own.functions, omittedMentions: [],
      modules: list(source.modules).filter((m) => record(m).location !== own.location) };
    const ownPath = join(work, "own.json"), ownGiven = join(work, "own-given.jsonl");
    const ownModule = join(work, "own-module.json");
    writeFileSync(ownModule, JSON.stringify(own));
    writeFileSync(ownPath, JSON.stringify(ownAst));
    const prefix = `module:${String(own.location)}#`;
    const lines = readFileSync(given, "utf8").split("\n").filter(Boolean).map((s) => {
      const value: unknown = JSON.parse(s), line = record(value);
      if (typeof line.unit !== "string") throw Error("missing unit");
      if (line.unit.startsWith(prefix)) line.unit = line.unit.slice(prefix.length);
      else if (!line.unit.startsWith("module:")) return null;
      return line;
    }).filter((l) => l !== null);
    writeFileSync(ownGiven, lines.map((l) => JSON.stringify(l)).join("\n"));
    const ownResult = prepare(ownPath, { ...options, ownModule, given: ownGiven, work: join(work, "own") });
    assert.deepEqual(ownResult.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
      first.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
    assert.equal(readFileSync(ownResult.path, "utf8"), original);
    log("own-file normalization: complete component keys and results equal imported path");

    const reversed = parsed(fragment);
    reversed.modules = [...list(reversed.modules)].reverse();
    const reversedPath = join(work, "reversed.json");
    writeFileSync(reversedPath, JSON.stringify(reversed));
    const reordered = prepare(reversedPath, { ...options, work: join(work, "reordered") });
    assert.deepEqual(reordered.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
      first.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
    assert.equal(readFileSync(reordered.path, "utf8"), original);
    log("importer module ordering: identical canonical component requests and results");

    // Root selection cannot manufacture a partial canonical interface.
    const noRoots = prepare(fragment, { ...options, names: "%absent-interface-control",
      work: join(work, "no-roots") });
    assert.deepEqual(parsed(noRoots.path), { modules: [] });
    assert(noRoots.records.every((r) => r.record.stage === "interface-plan"));
    const selectedOwn = prepare(ownPath, { ...options, names: "%absent-interface-control",
      ownModule, given: ownGiven, work: join(work, "selected-own") });
    assert.equal(readFileSync(selectedOwn.path, "utf8"), readFileSync(ownResult.path, "utf8"));
    assert.deepEqual(selectedOwn.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
      ownResult.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
    log("selected roots: no unrelated component; own publication retains complete canonical keys");

    // Forced executions also publish: timing text must not make one exact
    // importer request produce two different stored payloads.
    const importerSource = parsed(fragment);
    const firstFunction = record(list(importerSource.functions)[0]);
    const deterministic = verifierCall(verifierBuild, ["--verify-interface-stage", "8", fragment, first.path,
      given, empty, String(importerSource.file), "12", String(firstFunction.name)]);
    const once = invoke(deterministic, options.invocation);
    const twice = invoke(deterministic, { ...options.invocation, force: true });
    assert.equal(once.stdout, twice.stdout);
    assert.equal(once.stderr, twice.stderr);
    assert.equal(twice.record.execution, "executed");
    log("importer forced execution: identical semantic payload, measurement output excluded");

    const timeoutRequest = parsed(join(options.work, "component-0.json"));
    timeoutRequest.force = ["timeout-control"];
    const timeoutPath = join(work, "timeout-request.json");
    writeFileSync(timeoutPath, JSON.stringify(timeoutRequest));
    const timed = invokeProcess(verifierCall(verifierBuild, ["--module-interface", timeoutPath]),
      { ...options.invocation, limitMs: 1 });
    assert.equal(timed.record.execution, "timed-out");
    assert(timed.record.key);
    assert(!existsSync(join(store, "entries", "module-interface", timed.record.key)));
    const malformed = join(work, "malformed.json");
    writeFileSync(malformed, "{}");
    const failed = invokeProcess(verifierCall(verifierBuild, ["--module-interface", malformed]), options.invocation);
    assert.equal(failed.record.execution, "failed");
    assert(failed.record.key);
    assert(!existsSync(join(store, "entries", "module-interface", failed.record.key)));
    log("timeout and malformed request: no finished interface published");
  } finally {
    if (previous === undefined) delete process.env.TSCERT_STAGE_STORE;
    else process.env.TSCERT_STAGE_STORE = previous;
  }
}
