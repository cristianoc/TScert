import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import vm from "node:vm";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
import { stripTypes } from "../tools/strip-types.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { producerExecutable } from "./verify-source.mts";

/** Reachable pattern defaults require claims even when a producer omits them. */
export function checkPatternDefaults(verifier: string, artifacts: string): void {
  const ast: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
  const claims: SourceClaims = JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
  const statement = ast.functions.find((f) => f.name === "optionalDefault")?.body[0];
  assert(statement?.k === "destructure" && statement.target.k === "object");
  const fallback = statement.target.props[0]?.default_;
  assert(fallback);
  const fn = claims.functions.find((f) => f.name === "optionalDefault");
  assert(fn);
  const before = fn.expressions.length;
  fn.expressions = fn.expressions.filter((e) =>
    e.pos[0] !== fallback.pos[0] || e.pos[1] !== fallback.pos[1]);
  assert.equal(fn.expressions.length, before - 1);
  const forged = join(artifacts, "missing-pattern-default-claims.json");
  writeFileSync(forged, JSON.stringify(claims));
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(verifier, [mode, join(artifacts, "fragment.json"), forged,
      join(artifacts, "source.ts"), join(artifacts, "evidence.json"),
      ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    assert.match(result.stdout + result.stderr, /no claimed type for the expression/);
  }
  const source = stripTypes(readFileSync(join(artifacts, "source.ts"), "utf8"))
    .replace(/^export /gm, "");
  assert.equal(vm.runInNewContext(source + "\noptionalDefault({})"), false);
  assert.equal(vm.runInNewContext(source + "\noptionalDefault({ f: 3 })"), 3);
  assert.equal(vm.runInNewContext(source +
    "\nconst state = { value: null }; skippedEffect({ f: 3 }, state); state.value"), 1);
  console.log("pattern defaults: skipped effects, reachable fallback and omitted-claim refusal checked");
}

/** The producer's refusal is not the verifier's protection. Forge a claim for
 * the later read and require both Lean entry points to reject its scope. */
export function checkDefaults(verifier: string, artifacts: string): void {
  const source = join(artifacts, "source.ts");
  const ast: Ast = JSON.parse(
    readFileSync(join(artifacts, "fragment.json"), "utf8"),
  );
  const claims: SourceClaims = JSON.parse(
    readFileSync(join(artifacts, "claims.json"), "utf8"),
  );
  const first = ast.functions[0]?.body[0];
  assert(first?.k === "const");
  const lambda = first.bindings[0]?.init;
  assert(lambda?.k === "lambda");
  const param = lambda.params[0];
  assert(param?.default);
  const pos = param.default.pos;
  param.default = { k: "id", pos, name: "second" };
  const point = claims.functions[0]?.expressions.find(
    (e) => e.pos[0] === pos[0] && e.pos[1] === pos[1],
  );
  assert(point);
  point.type = [1, 2, 3]; // boolean | undefined, the later parameter's type.
  const badAst = join(artifacts, "later-default-ast.json");
  const badClaims = join(artifacts, "later-default-claims.json");
  writeFileSync(badAst, JSON.stringify(ast));
  writeFileSync(badClaims, JSON.stringify(claims));
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        badAst,
        badClaims,
        source,
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    assert.match(
      result.stdout + result.stderr,
      /parameter default may only read initialized earlier parameters/,
    );
  }

  const examples = join(import.meta.dirname, "examples");
  const execute = (file: string, expression: string) =>
    vm.runInNewContext(
      stripTypes(readFileSync(join(examples, `${file}.ts`), "utf8")) +
        "\n" +
        expression,
      {},
      { timeout: 1000 },
    );
  assert.throws(
    () => execute("default-later-parameter", "laterDefault()"),
    /Cannot access 'second' before initialization/,
  );
  assert.throws(
    () => execute("invalid-default-invocation", "defaultInvokedTooEarly()"),
    /Cannot access 'later' before initialization/,
  );
  assert.equal(execute("generic-default", "genericDefault(true)"), null);
  assert.equal(
    execute("generic-rigid-default", "undefinedRigidDefault(undefined)"),
    undefined,
  );
  for (const seed of [true, false]) {
    assert.equal(
      execute("generic-rigid-default", `genericDeferredDefault(${seed})`),
      seed,
    );
    // Both formerly gated safe defaults now verify.
    assert.equal(
      execute("default-deferred-capture", `deferredDefaultCapture(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-deferred-capture", `deferredChain(${seed})`),
      false,
    );
    assert.equal(
      execute("generic-rigid-default", `rigidDefault(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultResult(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultCallback(${seed})`),
      seed,
    );
    assert.equal(
      execute("generic-defaults", `genericDefaultValue(${seed})`),
      false,
    );
    assert.equal(
      execute("default-parameter-scope", `initializedDefaults(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-parameter-scope", `defaultEffects(${seed})`),
      false,
    );
    assert.equal(
      execute("default-parameter-scope", `suppliedDefaultSkipsEffect(${seed})`),
      seed,
    );
    assert.equal(
      execute("default-parameter-scope", `nonTrailingDefault(${seed})`),
      seed,
    );
  }
  console.log(
    "default initialization: ordered scope, effects, skipped defaults and forged later read checked",
  );
}

/** A generic closure's default is part of its graph code, checked with the
 * code: production fails at the default's write of `null`, located there, and
 * consumption accepts no evidence for the program, which production cannot
 * emit. */
export function checkSchemeDefaults(verifier: string, artifacts: string): void {
  writeFileSync(join(artifacts, "evidence.json"), "{}");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        join(artifacts, "fragment.json"),
        join(artifacts, "claims.json"),
        join(artifacts, "source.ts"),
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    if (mode === "--check-source-claims") continue;
    assert.match(
      result.stdout + result.stderr,
      /source expression obligation at \[400,419\)/,
    );
    const diagnostic = readDiagnostic(result.stdout + result.stderr);
    assert(diagnostic?.kind === "node-typing");
    assert.deepEqual(diagnostic.source.sourceMap?.pos, [400, 419]);
  }
}

/** A proposed well-typed closure still cannot read its capture during TDZ.
 * This must be a located refusal from both independent entry points. */
export function checkEarlyDefault(verifier: string, artifacts: string): void {
  const sanitized: Ast = JSON.parse(readFileSync(join(artifacts, "fragment.json"), "utf8"));
  const statement = sanitized.functions[0]?.body[0];
  assert(statement?.k === "const");
  const lambda = statement.bindings[0]?.init;
  assert(lambda?.k === "lambda");
  const parameter = lambda.params[1];
  assert(parameter?.default?.k === "apply");
  parameter.default = { k: "lit", pos: parameter.default.pos, lit: { a: "booleanlit", v: "true" } };
  // A safe initializer supplies a complete proposal with the original source
  // identities; both entry points check the original initializer's scope.
  const donor = join(artifacts, "safe-default-ast.json");
  const flow = join(artifacts, "safe-default-flow.json");
  writeFileSync(donor, JSON.stringify(sanitized));
  const lowered = spawnSync(verifier, ["--lower-control-flow", donor],
    { encoding: "utf8", timeout: 30_000 });
  assert.ifError(lowered.error);
  assert.equal(lowered.status, 0, lowered.stdout + lowered.stderr);
  writeFileSync(flow, lowered.stdout);
  const proposed = spawnSync(producerExecutable, [donor, flow],
    { encoding: "utf8", timeout: 30_000 });
  assert.ifError(proposed.error);
  assert.equal(proposed.status, 0, proposed.stdout + proposed.stderr);
  writeFileSync(join(artifacts, "claims.json"), proposed.stdout);
  writeFileSync(join(artifacts, "evidence.json"), "{}");
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const result = spawnSync(
      verifier,
      [
        mode,
        join(artifacts, "fragment.json"),
        join(artifacts, "claims.json"),
        join(artifacts, "source.ts"),
        join(artifacts, "evidence.json"),
        ...(mode === "--produce-source-claims" ? ["12"] : []),
      ],
      { encoding: "utf8", timeout: 30_000 },
    );
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    assert.equal(result.status, 1);
    const output = result.stdout + result.stderr;
    assert.match(output, /pending closure cannot be invoked or exposed/);
    const diagnostic = readDiagnostic(output);
    assert(diagnostic?.kind === "source-refusal");
    assert.equal(diagnostic.sourceMap.role, "binding-annotation");
    assert.deepEqual(diagnostic.sourceMap.pos, lambda.pos);
  }
}
