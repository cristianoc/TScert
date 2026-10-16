import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import type { SourceClaims } from "../tools/source-claims.mts";

/** A type parameter typing a value and a rest is instantiated at an array or
 * tuple type, whose argument lists the rest's are: a forged instance that is
 * no array, at the call or `new` whose text starts with `at`, is refused by
 * both verifier entry points, not read as a pack. */
export function checkRestPackInstance(verifier: string, artifacts: string, at: string): void {
  const claims: SourceClaims = JSON.parse(readFileSync(join(artifacts, "claims.json"), "utf8"));
  const source = readFileSync(join(artifacts, "source.ts"), "utf8");
  const start = source.indexOf(at);
  assert(start >= 0);
  const forged = structuredClone(claims);
  const call = forged.functions.flatMap((f) => f.expressions).find((e) => e.pos[0] === start && e.instantiate);
  assert(call?.instantiate?.length === 1, `${at} names its one instance`);
  // The Boolean rows: no array.
  call.instantiate[0].type = [1, 2];
  const claimed = join(artifacts, "forged-pack-instance-claims.json");
  writeFileSync(claimed, JSON.stringify(forged));
  for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
    const p = spawnSync(verifier, [mode, join(artifacts, "fragment.json"), claimed, join(artifacts, "source.ts"),
      join(artifacts, "evidence.json"), ...(mode === "--produce-source-claims" ? ["12"] : [])],
      { encoding: "utf8", timeout: 30_000 });
    assert.ifError(p.error);
    assert.equal(p.status, 1, p.stdout + p.stderr);
    assert.match(p.stdout + p.stderr, /a type parameter typing a value and a rest's argument list, is no array or tuple type/);
  }
}
