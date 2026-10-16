import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import type { SourceClaims } from "../tools/source-claims.mts";

/** Per-signature claims cross the same independent boundary as ordinary claims. */
export function checkOverloads(verifier: string, artifacts: string): void {
  const original: SourceClaims = JSON.parse(
    readFileSync(join(artifacts, "claims.json"), "utf8"),
  );
  const edits = new Map<string, (c: SourceClaims) => void>([
    [
      "duplicate owner",
      (c) => {
        const f = c.functions[0];
        assert(f?.arrows?.[0]);
        f.arrows.push(structuredClone(f.arrows[0]));
      },
    ],
    [
      "nonclosure owner",
      (c) => {
        const f = c.functions[0];
        assert(f?.arrows?.[0]);
        f.arrows[0].pos = f.namePos;
      },
    ],
    [
      "invalid row label",
      (c) => {
        const e = c.functions[0]?.arrows?.[0]?.rows[0]?.expressions[0];
        assert(e);
        e.type = [c.types.length];
      },
    ],
    [
      "duplicate expression",
      (c) => {
        const r = c.functions[0]?.arrows?.[0]?.rows[0];
        assert(r?.expressions[0]);
        r.expressions.push(structuredClone(r.expressions[0]));
      },
    ],
    [
      "foreign expression",
      (c) => {
        const r = c.functions[0]?.arrows?.[0]?.rows[0];
        const foreign = c.functions[1]?.expressions[0];
        assert(r && foreign);
        r.expressions.push(structuredClone(foreign));
      },
    ],
    [
      "row substitution",
      (c) => {
        const e = c.functions[0]?.arrows?.[0]?.rows[0]?.expressions[0];
        assert(e);
        e.instantiate = [{ name: "T", type: [1, 2], resolution: null }];
      },
    ],
    [
      "invalid row refinement",
      (c) => {
        const e = c.functions[0]?.arrows?.[0]?.rows[0]?.expressions[0];
        assert(e);
        e.current = [["value", [c.types.length]]];
      },
    ],
    [
      "forged captured contents",
      (c) => {
        const f = c.functions.find((f) => f.name === "overloadCapture");
        const bindings =
          f?.arrows?.[0]?.rows.flatMap((r) =>
            r.entries.flatMap((e) => e.bindings),
          ) ?? [];
        const cells = bindings.filter((b) => b.name === "cell");
        assert(cells.length > 0);
        for (const cell of cells) cell.current = [["value", [1]]];
      },
    ],
    [
      "missing signature row",
      (c) => {
        const a = c.functions[0]?.arrows?.[0];
        assert(a);
        a.rows.pop();
      },
    ],
  ]);
  for (const [name, edit] of edits) {
    const claims = structuredClone(original);
    edit(claims);
    const file = join(artifacts, "forged-overload.json");
    writeFileSync(file, JSON.stringify(claims));
    for (const mode of ["--produce-source-claims", "--check-source-claims"]) {
      const p = spawnSync(
        verifier,
        [
          mode,
          join(artifacts, "fragment.json"),
          file,
          join(artifacts, "source.ts"),
          join(artifacts, "evidence.json"),
          ...(mode === "--produce-source-claims" ? ["12"] : []),
        ],
        { encoding: "utf8", timeout: 30_000 },
      );
      assert.ifError(p.error);
      assert.equal(p.signal, null);
      assert.equal(p.status, 1, `${name}: ${p.stdout}${p.stderr}`);
      assert.match(
        p.stdout + p.stderr,
        name === "foreign expression"
          ? /expression claim names a foreign or missing execution point/
          : /invalid source claims|per-arrow claim|per-arrow interior claims|evidence search failed|source evidence does not justify/,
      );
    }
  }
  console.log(
    `overload boundary: ${edits.size} forged documents refused by both entry points`,
  );
}
