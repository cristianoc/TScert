import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import vm from "node:vm";
import type { SourceClaims } from "../tools/source-claims.mts";
import type { Ast } from "../tools/fragment.mts";
import { stripTypes } from "../tools/strip-types.mts";

/** Universal collection, substitution and source binding are independent
 * obligations; neither fresh search nor reused evidence may bypass them. */
export function checkGenericRest(verifier: string, artifacts: string): void {
  const claims: SourceClaims = JSON.parse(
    readFileSync(join(artifacts, "claims.json"), "utf8"),
  );
  const ast: Ast = JSON.parse(
    readFileSync(join(artifacts, "fragment.json"), "utf8"),
  );
  const reject = (
    name: string,
    changed: SourceClaims,
    tree: Ast,
    reason: RegExp,
    reusedReason = reason,
  ) => {
    const claimed = join(artifacts, `${name}-claims.json`);
    const parsed = join(artifacts, `${name}-ast.json`);
    writeFileSync(claimed, JSON.stringify(changed));
    writeFileSync(parsed, JSON.stringify(tree));
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const p = spawnSync(
        verifier,
        [
          mode,
          parsed,
          claimed,
          join(artifacts, "source.ts"),
          join(artifacts, "evidence.json"),
          ...(mode === "--produce-source-claims" ? ["12"] : []),
        ],
        { encoding: "utf8", timeout: 30_000 },
      );
      assert.ifError(p.error);
      assert.equal(p.signal, null);
      assert.equal(p.status, 1, p.stdout + p.stderr);
      assert.match(p.stdout + p.stderr, mode === "--produce-source-claims" ? reason : reusedReason);
    }
  };
  const retyped = structuredClone(claims);
  const first = retyped.functions.find((f) => f.name === "genericRestUses");
  assert(first);
  const point = first.expressions.find(
    (e) => !Array.isArray(e.type) && "scheme" in e.type,
  );
  assert(point && !Array.isArray(point.type) && "scheme" in point.type);
  assert.deepEqual(point.type.scheme.rest, { param: "T" });
  point.type.scheme.rest = [1, 2];
  // The changed rest contract is checked at the numeric call's source
  // obligation; reused evidence must also decode over its changed type table.
  reject(
    "retyped-rest",
    retyped,
    ast,
    /source expression obligation at \[261,268\): evidence search failed/,
    /head \d+ argument 0 part 0: head \d+ binds 0 locals, slot 0 named/,
  );

  const wrongCall = structuredClone(claims);
  const fn = wrongCall.functions.find((f) => f.name === "genericRestUses");
  assert(fn);
  const calls = fn.expressions.filter((e) => e.instantiate);
  assert.equal(calls.length, 2);
  const numericStart = readFileSync(join(artifacts, "source.ts"), "utf8").indexOf("collect(n, n)");
  assert(numericStart >= 0);
  const numeric = calls.find((e) => e.pos[0] === numericStart)?.instantiate?.[0];
  assert(numeric);
  numeric.type = [1, 2];
  // Fresh search fails at the obligation; reused evidence names heads of the
  // unmutated claims' equations, so it no longer decodes over the new ones.
  reject(
    "wrong-rest-instance",
    wrongCall,
    ast,
    /evidence search failed|does not justify|head \d+ takes \d+ arguments, given \d+/,
  );

  const fixed = structuredClone(ast);
  const body = fixed.functions.find((f) => f.name === "genericRestUses")
    ?.body[0];
  assert(body?.k === "const");
  const lambda = body.bindings[0]?.init;
  assert(lambda?.k === "lambda");
  const rest = lambda.params[0];
  assert(rest?.rest);
  delete rest.rest;
  // Without its rest the closure is graph code at its claimed scheme, whose
  // variadic signature the source annotation no longer states.
  reject(
    "lost-rest-binding",
    claims,
    fixed,
    /closure signature claim is outside the source annotation/,
  );

  const early = structuredClone(ast);
  const defBody = early.functions.find((f) => f.name === "ordinaryDefaultRest")
    ?.body[0];
  assert(defBody?.k === "const");
  const defLambda = defBody.bindings[0]?.init;
  assert(defLambda?.k === "lambda");
  const firstDefault = defLambda.params[0];
  assert(firstDefault?.default);
  firstDefault.default = { k: "id", pos: firstDefault.default.pos, name: "xs" };
  reject(
    "early-rest-read",
    claims,
    early,
    /parameter default may only read initialized earlier parameters/,
  );

  const restDefault = structuredClone(ast);
  const restBody = restDefault.functions.find(
    (f) => f.name === "ordinaryDefaultRest",
  )?.body[0];
  assert(restBody?.k === "const");
  const restLambda = restBody.bindings[0]?.init;
  assert(restLambda?.k === "lambda");
  const lastParam = restLambda.params[1];
  assert(lastParam?.rest && restLambda.params[0]?.default);
  lastParam.default = restLambda.params[0].default;
  reject(
    "default-on-rest",
    claims,
    restDefault,
    /a rest parameter cannot have a default/,
  );

  // Operand claims in a generic body are checked, not silently discarded.
  const operand = structuredClone(claims);
  const callback = operand.functions.find(
    (f) => f.name === "genericRestCallback",
  );
  assert(callback);
  const actual = callback.expressions.find(
    (e) => !Array.isArray(e.type) && "param" in e.type,
  );
  assert(actual);
  actual.type = [1, 2];
  reject(
    "forged-rigid-operand",
    operand,
    ast,
    /evidence search failed|does not justify/,
  );

  const source = stripTypes(readFileSync(join(artifacts, "source.ts"), "utf8"));
  const evaluate = (expression: string): unknown =>
    vm.runInNewContext(source + "\n" + expression, {}, { timeout: 1000 });
  assert.equal(evaluate("JSON.stringify(genericRestUses(true, 7))"), "[7,7]");
  assert.equal(
    evaluate("JSON.stringify(genericRestPrefix(false, 7))"),
    "[7,7]",
  );
  assert.equal(evaluate("JSON.stringify(genericDefaultRest(true, 7))"), "[7]");
  assert.equal(
    evaluate(
      "const xs = genericRestSpread([true,,false]); xs.length === 3 && Object.hasOwn(xs, 1) && xs[1] === undefined",
    ),
    true,
  );
  assert.equal(
    evaluate(
      "const a = genericRestDeclaration(0, 1); const b = genericRestDeclaration(0, 2); a[0] = 3; b[0] === 2",
    ),
    true,
  );
  process.stdout.write(
    "quantified rest: source binding, universal contract, substitutions, operands and runtime collection checked\n",
  );
}
