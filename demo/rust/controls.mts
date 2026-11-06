// Forged Rust Fragments reuse honest evidence and bypass Node's comparison.
// These are source/evidence controls, not checks of a link-table assembly.
import assert from "node:assert/strict";
import { writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { front, check } from "./stages.mts";
import { tested } from "../../pipeline/stages.mts";
import { verifierBuild, verifierCall } from "../../pipeline/stage-execution.mts";
import type { Ast } from "../../tools/fragment.mts";

/** Honest model evidence cannot justify a different signature, body or
 * captured callee association. */
export function checkRustForgeries(): void {
  const file = join(import.meta.dirname, "examples/rust-i64-calls.rs");
  const input = front(file);
  assert.ok(!("refused" in input));
  const honest = check(file, input.source, input.fragment);
  assert.equal(honest.status, "verified", JSON.stringify(honest));
  const checkFragment = (name: string, mutate: (ast: Ast) => void): void => {
    const ast = structuredClone(input.fragment);
    mutate(ast);
    const path = join(honest.artifacts, `forged-${name}.json`);
    writeFileSync(path, JSON.stringify(ast));
    const result = tested(verifierCall(verifierBuild, ["--check-units", path,
      join(honest.artifacts, "claims.json"), resolve(file), join(honest.artifacts, "evidence.json")]), 60_000);
    assert.equal(result.status, 1, `${name}: ${result.stdout}${result.stderr}`);
    assert.match(result.stdout + result.stderr, /reject:|"accepted":false/, name);
  };
  checkFragment("signature", ast => {
    const fn = ast.functions.find(f => f.name === "forward");
    assert.ok(fn);
    fn.retType = { k: "atom", name: "string", span: fn.namePos };
  });
  checkFragment("code", ast => {
    const fn = ast.functions.find(f => f.name === "forward");
    assert.ok(fn);
    const last = fn.body.at(-1);
    assert.ok(last?.k === "return");
    last.e = { k: "lit", pos: last.pos, lit: { a: "stringlit", v: "wrong result" } };
  });
  checkFragment("capture-association", ast => {
    // The source capture named identity is associated with the string body.
    const target = ast.functions.find(f => f.name === "text");
    const identity = ast.functions.find(f => f.name === "identity");
    assert.ok(target && identity);
    [target.name, identity.name] = [identity.name, target.name];
  });
  checkFragment("call-target", ast => {
    const fn = ast.functions.find(f => f.name === "forward");
    assert.ok(fn);
    const last = fn.body.at(-1);
    assert.ok(last?.k === "return" && last.e?.k === "apply");
    const callee = last.e.callee;
    assert.ok(callee.k === "id");
    callee.name = "text";
  });
}
