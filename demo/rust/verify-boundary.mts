// The demo's boundary check: a Rust crate exported by `wasm-bindgen`
// (`lib.rs`), the declaration it ships (`lib.d.ts`), and a TypeScript caller
// importing from `./lib.js` (`caller.ts`), in one directory with its strict
// `tsconfig.json`. It checks
//   (a) the crate's functions in the model, each export at its signature;
//   (b) the caller through TScert's TypeScript pipeline, each import assumed
//       at the declaration TypeScript resolves it to;
//   (c) source-bound Lean assembly: retained signatures, accepted invocation
//       bodies, concrete captures and entry slots, and both graph attachments.
// Node also compares wasm-bindgen signatures for mismatch diagnostics.
// What these establish together, and what they assume, is stated in this
// directory's README.
//
// Usage: node demo/rust/verify-boundary.mts <dir>

import { spawnSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import type { TypeTerm, ValueRoot } from "../../tools/declaration-types.mts";
import { readFragmentFile } from "../../pipeline/verify-source.mts";
import { ordinaryEffect } from "../../tools/type-graph.mts";
import type { RFn, RType } from "./parse.mts";
import { check, front, print, readable, type Report } from "./stages.mts";

const here = import.meta.dirname;

/** `wasm-bindgen`'s type for a Rust type of the subset, by position; null where it is refused. */
function boundaryAtom(t: RType, position: "parameter" | "result"): TypeTerm | null {
  if (t.k !== "prim") return null; // an exported struct is a class owning wasm memory
  if (t.name === "&str" && position === "result") return null; // no borrowed `str` result
  const name = t.name === "i64" ? "bigint" : t.name === "bool" ? "boolean" : t.name === "String" || t.name === "&str" ? "string" : "number";
  return { k: "atom", name, span: t.span };
}

/** The signature `wasm-bindgen`'s mapping gives an export, or why there is none. */
function rustSignature(f: RFn): TypeTerm | string {
  const params: TypeTerm[] = [];
  for (const p of f.params) {
    const atom = boundaryAtom(p.type, "parameter");
    if (atom === null) return `parameter ${p.name}: its type is outside wasm-bindgen's mapping of the subset`;
    params.push(atom);
  }
  const result = f.ret && boundaryAtom(f.ret, "result");
  if (result === null) return "its result type is outside wasm-bindgen's mapping of the subset";
  return { k: "function", effect: ordinaryEffect, receiver: null, params, rest: null, result, span: f.span };
}

/** The first path at which `a` and `b` differ, spans aside; null where they agree. */
function difference(a: unknown, b: unknown, path: string): string | null {
  if (typeof a !== "object" || typeof b !== "object" || a === null || b === null)
    return a === b ? null : `${path}: ${JSON.stringify(a)} against ${JSON.stringify(b)}`;
  if (Array.isArray(a) !== Array.isArray(b)) return `${path}: an array against a non-array`;
  const keys = new Set([...Object.keys(a), ...Object.keys(b)].filter((k) => k !== "span"));
  for (const k of keys) {
    const d = difference(Reflect.get(a, k), Reflect.get(b, k), `${path}.${k}`);
    if (d !== null) return d;
  }
  return null;
}

const field = (value: unknown, name: string): unknown =>
  typeof value === "object" && value !== null && name in value ? Reflect.get(value, name) : undefined;

/** The caller through `pipeline/verify-source.mts`: its report and its Fragment's imported values. */
function checkCaller(dir: string): { report: Report; values: ValueRoot[] } {
  const source = readFileSync(join(dir, "caller.ts"), "utf8");
  const ran = spawnSync("node", [join(here, "../../pipeline/verify-source.mts"), join(dir, "caller.ts"), "--project", dir],
    { encoding: "utf8", maxBuffer: 1 << 26, timeout: 240_000 });
  if (ran.error) throw ran.error;
  const out: unknown = JSON.parse(ran.stdout);
  const status = field(out, "status"), artifacts = field(out, "artifacts");
  if (typeof artifacts !== "string" ||
      (status !== "verified" && status !== "unsupported" && status !== "unverified" && status !== "error"))
    throw Error(`verify-source printed no outcome: ${ran.stderr}`);
  if (status === "verified" && ran.status !== 0)
    throw Error(`verify-source reported verified but exited ${ran.status}: ${ran.stderr}`);
  const unitsOut = field(out, "units");
  const units = (Array.isArray(unitsOut) ? unitsOut : []).map((u: unknown) => {
    const unit = field(u, "unit"), s = field(u, "status"), detail = field(u, "detail");
    return { unit: String(unit), status: String(s), detail: typeof detail === "string" && detail !== "" ? readable(detail, source) : "" };
  });
  const detail = field(out, "detail");
  const report: Report = { status, artifacts, units };
  if (units.length === 0 && typeof detail === "string") report.detail = detail.split("\n")[0] ?? "";
  const fragment = join(artifacts, "fragment.json");
  const values = existsSync(fragment) ? readFragmentFile(fragment).declarations.values : [];
  return { report, values };
}

/** (c): each value the caller imports from `lib.d.ts` against the crate's export of its name. */
function agreement(values: ValueRoot[], exports: Map<string, RFn>): string[] {
  const refusals: string[] = [];
  const imports = values.filter((v) => v.declaration.module === "./lib.d.ts");
  if (imports.length === 0) refusals.push("the caller imports no Rust export through ./lib.d.ts");
  for (const v of imports) {
    const name = v.declaration.name;
    const label = `${v.binding.local} (lib.d.ts: ${name})`;
    const f = exports.get(name);
    if (f === undefined) { refusals.push(`${label}: lib.rs exports no #[wasm_bindgen] function of that name`); continue; }
    if (v.construct || v.typeParams.length > 0) {
      refusals.push(`${label}: a construct signature or a generic declaration`);
      continue;
    }
    const declared = v.type;
    if (declared.k !== "function") { refusals.push(`${label}: not one function signature (overloads?)`); continue; }
    const signature = rustSignature(f);
    if (typeof signature === "string") continue;
    const d = difference(declared, signature, "signature");
    if (d === null) continue;
    let explanation = d;
    let parameterMismatch = false;
    if (signature.k === "function") {
      for (const [index, expected] of signature.params.entries()) {
        const actual = declared.params[index];
        const parameter = f.params[index];
        if (actual?.k === "atom" && expected.k === "atom" && actual.name !== expected.name && parameter?.type.k === "prim") {
          explanation = `parameter ${parameter.name}: lib.d.ts states ${actual.name}; Rust ${parameter.type.name} requires ${expected.name} in JavaScript`;
          parameterMismatch = true;
          break;
        }
      }
    }
    if (!parameterMismatch && signature.k === "function" && declared.result.k === "atom" && signature.result.k === "atom" &&
        declared.result.name !== signature.result.name && f.ret?.k === "prim")
      explanation = `result: lib.d.ts states ${declared.result.name}; Rust ${f.ret.name} requires ${signature.result.name} in JavaScript`;
    refusals.push(`${label}: ${explanation}`);
  }
  return refusals;
}

/** Lean rechecks the exact Fragment, claims and evidence artifacts and
 * constructs the linked model consumed by Demo.linked_safe. */
function leanAgreement(rust: Report, caller: Report): string[] {
  const binary = join(here, "../../lean/.lake/build/bin/boundary-check");
  const checked = spawnSync(binary, [rust.artifacts, caller.artifacts],
    { encoding: "utf8", timeout: 60_000, maxBuffer: 1 << 20 });
  return checked.error || checked.status !== 0 || checked.stdout.trim() !== "linked"
    ? [`Lean linked assembly refused: ${checked.error?.message ?? checked.stderr.trim()}`]
    : [];
}

const [dir] = process.argv.slice(2);
if (dir === undefined) {
  process.stderr.write("usage: node demo/rust/verify-boundary.mts <dir>\n");
  process.exit(2);
}
const rs = join(dir, "lib.rs");
const lowered = front(rs);
if ("refused" in lowered) {
  process.stdout.write(`unsupported: ${rs}\n  ${lowered.refused}\n`);
  process.exit(1);
}
const exports = new Map(lowered.crate.fns.filter((f) => f.exported).map((f) => [f.name, f]));
const mapping = [...exports.values()].flatMap((f) => {
  const s = rustSignature(f);
  return typeof s === "string" ? [`${f.name}: ${s}`] : [];
});

const rust = check(rs, lowered.source, lowered.fragment);
print(`${rs} (Rust functions in the model)`, rust);
const caller = checkCaller(dir);
print(`${join(dir, "caller.ts")} (caller, imports at lib.d.ts)`, caller.report);
const signatureRefusals = [...mapping, ...agreement(caller.values, exports)];
process.stdout.write(`${signatureRefusals.length === 0 ? "agreed" : "disagreed"}: lib.d.ts against lib.rs\n`);
for (const r of signatureRefusals) process.stdout.write(`  ${r}\n`);
const assemblyRefusals = leanAgreement(rust, caller.report);
process.stdout.write(`${assemblyRefusals.length === 0 ? "linked" : "refused"}: Lean source-bound assembly\n`);
for (const r of assemblyRefusals) process.stdout.write(`  ${r}\n`);

const ok = rust.status === "verified" && caller.report.status === "verified" &&
  signatureRefusals.length === 0 && assemblyRefusals.length === 0;
process.stdout.write(`${ok ? "passed" : "refused"}: Rust model, caller and declaration checks for ${dir}\n`);
process.exit(ok ? 0 : 1);
