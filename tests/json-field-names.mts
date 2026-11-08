// The parser, the OCaml producer and the Lean verifier exchange JSON documents:
// the Fragment tree with its declaration document, SourceClaims, the source
// flow, and the producer's qualified reads and explanations; Lean's equation
// trees are compared with their spelling in REQUEST-PROTOCOL.md. Each
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

let checked: number = 0;
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
    fact: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    form: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    slot: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    int: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    le: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    length: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    linear: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    either: "a disjunctive index fact, derived by EffectJson.lean",
    guarded: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    tag: "a guarded index fact's field, read by the instance EffectJson.lean states for HeapKnowledge.GuardTag's fact",
    path: "a linear term's field, read by the instance EffectJson.lean derives for HeapKnowledge.Term",
    ne: "an index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact and Linear.Fact",
    every: "a quantified index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact",
    stop: "a quantified index fact's field, read by the instance EffectJson.lean derives for HeapKnowledge.IndexFact",
    free: "a quantified fact's body variable, read by the instance EffectJson.lean derives for HeapKnowledge.Bound",
    t: "a quantified fact's body term, read by the instance EffectJson.lean derives for HeapKnowledge.Bound",
  });
}

// The SourceClaims document and its type table.
{
  const ts = declared(["tools/source-claims.mts", "tools/type-graph.mts", "tools/declaration-types.mts"]);
  const leanNames = lean(["lean/Verification/Source/Claims/Wire.lean",
    "lean/Verification/Source/ResolutionWire.lean", ...equationReaders], true);
  expectSubset("OCaml writes of SourceClaims", ocamlWrites("ocaml-producer/claims.ml"), ts, {});
  // The claims decoder's explicit reads: the other files' structures are
  // the verifier's own state, which the set above also holds.
  expectSubset("Lean reads of SourceClaims", lean(["lean/Verification/Source/Claims/Wire.lean"], true), ts, {});
  // The description's types, above its decoder.
  expectSubset("SourceClaims fields Lean ignores",
    declared(["tools/source-claims.mts"], "export function decodeSourceClaims"), leanNames, {
    labels: "a tuple element's label, not a field",
    ref: "a body variable's term, read by the instance Wire.lean derives for the inductive BodyVariable",
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

// The producer's side documents: the qualified reads the pipeline writes for
// it (`verify-source.mts`), and the explanations `producer --explain` prints.
{
  const source = read("pipeline/verify-source.mts");
  const written = new Set((source.match(/JSON\.stringify\(reads\.map\(\(\{([^}]*)\}\)/)?.[1] ?? "")
    .split(",").map((n) => n.trim()).filter((n) => n !== ""));
  assert.ok(written.size > 0, "the qualified-reads document's writer is found");
  const reads = ocamlReads("ocaml-producer/producer.ml");
  expectSubset("OCaml reads of qualified reads", reads, written, {});
  expectSubset("Qualified-read fields OCaml ignores", written, reads, {});
  const explanation = declared([], undefined);
  for (const n of (source.match(/interface Explanation \{([^}]*)\}/)?.[1] ?? "").matchAll(/(\w+)\s*:/g)) explanation.add(n[1] ?? "");
  assert.ok(explanation.size > 0, "the explanation's declared type is found");
  const explained = ocamlWrites("ocaml-producer/producer.ml");
  expectSubset("OCaml writes of explanations", explained, explanation, {});
  expectSubset("Explanation fields OCaml omits", explanation, explained, {});
}

// The equation tree's spelling: Lean alone writes and reads it (the evidence
// bundle's labels), and REQUEST-PROTOCOL.md states it for every other reader.
{
  const protocol = read("docs/REQUEST-PROTOCOL.md");
  const table = protocol.slice(protocol.indexOf("**Tree spelling.**"), protocol.indexOf("Decoding refuses an unknown"));
  const documented = new Set([...table.matchAll(/"(\w+)":/g)].flatMap(captured));
  assert.ok(documented.size > 0, "the protocol's tree spelling table is found");
  const codec = "lean/Verification/Types/EquationJson.lean";
  const writes = new Set([...read(codec).matchAll(/\("(\w+)",/g)].flatMap(captured));
  const reads = lean([codec]);
  expectSubset("Lean writes of equation trees", writes, documented, {});
  expectSubset("Lean reads of equation trees", reads, documented, {});
  expectSubset("Tree fields Lean does not write", documented, writes, {});
  expectSubset("Tree fields Lean does not read", documented, reads, {});
}

process.stdout.write(`JSON field names: ${checked} comparisons agree across TypeScript, Lean and OCaml\n`);
