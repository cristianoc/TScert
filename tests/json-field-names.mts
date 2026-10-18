// The parser, the OCaml producer and the Lean verifier exchange JSON documents:
// the Fragment tree with its declaration document, and SourceClaims. Each
// document's fields are written three times: as TypeScript types, as Lean
// decoders, and as the OCaml producer's reads and writes. Nothing compiles one against another, so
// this compares, by text, the field names each one uses, and fails when a
// consumer reads a name no TypeScript type declares, or TypeScript declares a
// name Lean never reads. It checks names only; the suites still decide whether
// a document is understood.
//   node tests/json-field-names.mts
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";

const root = join(import.meta.dirname, "..");
const read = (file: string): string => readFileSync(join(root, file), "utf8");
/** A match's first group, the name each pattern below captures. */
const captured = (m: RegExpMatchArray): string[] => (m[1] === undefined ? [] : [m[1]]);

/** Property names a TypeScript file declares. */
const declared = (files: string[], before?: string): Set<string> => new Set(files.flatMap((file) =>
  [...(before ? read(file).split(before)[0] ?? "" : read(file)).replace(/\/\*[\s\S]*?\*\//g, "").replace(/\/\/.*/g, "")
    .matchAll(/(?<![\w.])([A-Za-z_]\w*)\??\s*:(?!:)/g)].flatMap(captured)));

/** Field names a Lean file reads or states: explicit field reads, exact field
 * lists and, where a file decodes structures with `FromJson`, their fields. */
const lean = (files: string[], structures: boolean = false, before?: string): Set<string> => new Set(files.flatMap((file) => {
  const s = (before ? read(file).split(before)[0] ?? "" : read(file)).replace(/\/-[\s\S]*?-\//g, "").replace(/--.*/g, "");
  const exact = [...s.matchAll(/fieldsExactly\s+\S+\s+\[([^\]]*)\]/g)]
    .flatMap((m) => [...(m[1] ?? "").matchAll(/"(\w+)"/g)].flatMap(captured));
  // Plain and parenthesized arguments separately, since one read can nest in
  // another's argument.
  const reads = [...s.matchAll(/\b(?:jField|field|str|arr|bool|jArr|jStr|jNat|jBool)\s+[^\s()]+\s+"(\w+)"/g),
    ...s.matchAll(/\b(?:jField|field|str|arr|bool|jArr|jStr|jNat|jBool)\s+\([^()]*\)\s+"(\w+)"/g),
    ...s.matchAll(/getObjVal\?\s+"(\w+)"/g),
    ...s.matchAll(/getObjValAs\?\s+\S+\s+"(\w+)"/g)].flatMap(captured);
  const fields = !structures ? [] : [...s.matchAll(/^structure\s+\w+[^\n]*?\s+where\n((?:[ \t]+.*\n|\n)+?)(?=\S)/gm)]
    .flatMap((m) => [...(m[1] ?? "").matchAll(/^[ \t]+(\w+)\s*:/gm)].flatMap(captured));
  return [...exact, ...reads, ...fields];
}));

/** Field names the OCaml producer reads from a document. */
const ocamlReads = (file: string): Set<string> => new Set([...read(file)
  .matchAll(/\b(?:field|text|items|List\.mem_assoc|List\.assoc_opt)\s+"(\w+)"/g)].flatMap(captured));

/** Field names the OCaml producer writes into an object. */
const ocamlWrites = (file: string): Set<string> => new Set([...read(file).matchAll(/"(\w+)",/g)].flatMap(captured));

const missing = (names: Set<string>, from: Set<string>, allowed: Record<string, string>): string[] =>
  [...names].filter((n) => !from.has(n) && !(n in allowed)).sort();

let checked = 0;
const expectSubset = (what: string, names: Set<string>, from: Set<string>, allowed: Record<string, string>): void => {
  assert.deepEqual(missing(names, from, allowed), [], `${what}: field names differ; update every side, or record why here`);
  // An exception that no longer applies is itself drift.
  for (const n of Object.keys(allowed)) assert(names.has(n) && !from.has(n), `${what}: stale exception '${n}'`);
  checked++;
};

// Equation lowering reads declarations and claim labels across these owners.
const equationReaders = [
  "lean/Verification/Source/EffectJson.lean",
  "lean/Verification/Source/Equations/Trees.lean",
  "lean/Verification/Source/Equations/Declarations.lean",
  "lean/Verification/Source/Equations/ClaimWire.lean",
  "lean/Verification/Source/Equations/State.lean",
  "lean/Verification/Source/Equations/Interning.lean",
  "lean/Verification/Source/Equations/Core.lean",
  "lean/Verification/Source/Equations/Annotations.lean",
  "lean/Verification/Source/Equations/Instances.lean",
  "lean/Verification/Source/Equations/Finishing.lean",
  "lean/Verification/Source/Equations/Source.lean",
  "lean/Verification/Source/Equations/Lowering.lean",
];

// The Fragment AST and its declaration document.
{
  const ts = declared(["tools/fragment.mts", "tools/declaration-types.mts", "tools/claim.mts"]);
  const leanNames = new Set([...lean(["lean/Verification/Source/Fragment.lean",
    "lean/Verification/Source/FragmentTypes.lean",
    ...equationReaders]), ...lean(["lean/Verification/Source/ResolutionWire.lean"], false, "inductive Certificate")]);
  expectSubset("Lean reads of the Fragment", leanNames, ts, {
    binder: "a source-claims label, read by equation lowering",
    decl: "a source-claims label, read by equation lowering",
    meet: "a source-claims label, read by equation lowering",
    types: "the source-claims document's rows, read by equation lowering",
  });
  expectSubset("OCaml reads of the Fragment", ocamlReads("ocaml-producer/source.ml"), ts, {});
  expectSubset("Fragment fields Lean ignores", ts, leanNames, {
    arguments: "a reference's argument spans are provenance",
    kind: "a root binding's kind is provenance",
    v: "a literal atom's value is read by the claim decoder",
  });
}

// The SourceClaims document and its type table.
{
  const ts = declared(["tools/source-claims.mts", "tools/type-graph.mts", "tools/declaration-types.mts"]);
  const leanNames = lean(["lean/Verification/Source/Claims/Wire.lean",
    "lean/Verification/Source/ResolutionWire.lean", ...equationReaders], true);
  expectSubset("OCaml writes of SourceClaims", ocamlWrites("ocaml-producer/claims.ml"), ts, {});
  expectSubset("SourceClaims fields Lean ignores", declared(["tools/source-claims.mts"]), leanNames, {
    labels: "a tuple element's label, not a field",
  });
}

// The claim-independent source execution graphs.
{
  const ts = declared(["tools/source-flow.mts"], "const invalid");
  const keys = read("lean/Verification/Types/Claim.lean")
    .match(/instance : ToJson PropKey where[\s\S]*?(?=instance : FromJson PropKey)/)?.[0] ?? "";
  const writes = new Set([...(read("lean/Verification/Source/FlowJson.lean") +
    read("lean/Verification/Source/ExpressionPlan.lean") + keys)
    .matchAll(/\("(\w+)",/g)].flatMap(captured));
  expectSubset("Lean writes of source flow", writes, ts, {});
  expectSubset("OCaml reads of source flow", new Set([...ocamlReads("ocaml-producer/flow.ml"),
    ...ocamlReads("ocaml-producer/execution.ml")]), ts, {});
  expectSubset("Source flow fields Lean omits", ts, writes, {});
}

process.stdout.write(`JSON field names: ${checked} comparisons agree across TypeScript, Lean and OCaml\n`);
