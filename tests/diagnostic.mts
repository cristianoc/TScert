// Diagnostic metadata has its own wire boundary, apart from proof acceptance.
import assert from "node:assert/strict";
import { readDiagnostic } from "../tools/diagnostic.mts";
import type { Json } from "../tools/calculus.mts";

const common: { [key: string]: Json } = {
  phase: "proof-search", outcome: { kind: "not-established" }, fuel: 12,
  types: [["str"]],
};
const sourceMap: Json = { pos: [0, 1], role: "test", environmentStart: null, context: [] };
const node: Json = { label: 0, sourceMap, node: null,
  claim: { context: [], type: [0] }, requiredKnowledge: null };
const sequent: Json = { context: [[0]], term: { var: { i: 0 } }, type: [0] };
const edge = (mapping: Json): { [key: string]: Json } => ({
  ...common, kind: "edge-coverage", id: "c", edgeIndex: 0, source: node, destination: node,
  transfer: { available: [[0]], target: { label: 0, mapping },
    booleanObservation: null, tagObservation: null },
});
const cases: { [key: string]: Json }[] = [
  { ...common, kind: "production-failure", failure: "failed" },
  { ...common, kind: "production-failure", failure: "budget", names: [[0, "String"]], requiredResult: [0],
    outcome: { kind: "exhausted", resource: { kind: "subtype-frontier", limit: 12, rounds: 2, visited: 3 } } },
  { ...common, kind: "source-refusal", id: "r", sourceMap, reason: "unsupported" },
  { ...common, kind: "expression-claim", id: "e", sourceMap, sequent },
  { ...common, kind: "node-typing", id: "n", source: node, sequent },
  { ...common, kind: "direct-obligation", id: "d", sourceMap,
    judgment: { kind: "subtyping", subject: [0, 1], actual: [0], expected: [0] } },
  edge([0]),
  edge(null),
];
for (const value of cases) {
  const decoded = readDiagnostic(`obligation-diagnostic: ${JSON.stringify(value)}`);
  assert.ok(decoded, JSON.stringify(value));
  if (decoded.kind === "node-typing" || decoded.kind === "expression-claim") {
    assert.deepEqual(decoded.sequent.term, { kind: "var", i: 0 });
    assert.deepEqual(decoded.sequent.context, [[0]]);
    assert.deepEqual(decoded.sequent.type, [0]);
  } else {
    assert.deepEqual(decoded, value);
  }
}
for (const kind of ["source-refusal", "expression-claim", "direct-obligation"]) {
  const value = cases.find(v => typeof v === "object" && v !== null && !Array.isArray(v) && v.kind === kind);
  assert.ok(typeof value === "object" && value !== null && !Array.isArray(value));
  assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...value, sourceMap: null })}`), undefined);
}
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  kind: "node-typing", id: "n", source: null, sequent })}`), undefined);
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  kind: "production-failure", failure: "failed", unexpected: true })}`), undefined);
const invalidMappings: Json[] = ["", [-1], [0.5], [1], [true]];
for (const mapping of invalidMappings) {
  assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify(edge(mapping))}`), undefined);
}
for (const phase of ["proof-search", "certificate-check", "request-validation"]) {
  const value = { ...common, phase, kind: "production-failure", failure: "failed" };
  assert.deepEqual(readDiagnostic(`obligation-diagnostic: ${JSON.stringify(value)}`), value);
}
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  phase: "invalid", kind: "production-failure", failure: "failed" })}`), undefined);

const heap = readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  kind: "node-typing", id: "heap", sequent,
  source: { label: 0, sourceMap, node: null, claim: null,
    requiredKnowledge: {
      cells: [{ slot: 0, field: "id", contents: ["str", { strLit: { value: "checked" } },
        { numLit: { bits: "0" } }, { tag: { test: "isStr", answer: true } }] }],
      values: [], links: [{ cell: 0, value: 1, alias: false, field: "id", optional: false }],
      separation: { depth: 2, facts: [{ slot: 0, fields: ["id"], partners: [[1, ["id"]]] }] },
    } },
})}`);
assert.ok(heap?.kind === "node-typing");
assert.deepEqual(heap.source.requiredKnowledge?.cells[0].contents, ["str", { strLit: { value: "checked" } },
  { numLit: { bits: "0" } }, { tag: { test: { kind: "isStr" }, answer: true } }]);

console.log("Diagnostic decoder: all variants, heap data and malformed required fields");
