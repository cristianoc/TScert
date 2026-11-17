// Diagnostic metadata has its own wire boundary, apart from proof acceptance.
import assert from "node:assert/strict";
import { readDiagnostic, type ObligationDiagnostic } from "../tools/diagnostic.mts";
import type { Json } from "../tools/calculus.mts";

const common: { [key: string]: Json } = {
  phase: "proof-search", outcome: { kind: "not-established" }, fuel: 12,
  types: [["str"]],
};
const sourceMap: Json = { pos: [0, 1], role: "test", environmentStart: null, context: [] };
const node: Json = { label: 0, sourceMap, node: null,
  claim: { context: [], type: [0] }, requiredKnowledge: null };
const emptyKnowledge: Json = { cells: [], values: [], links: [], separation: { depth: 0, facts: [] }, elems: [], indices: [] };
const edgeFacts: Json = { requirement: { kind: "facts" }, established: emptyKnowledge, lacking: emptyKnowledge,
  known: emptyKnowledge };
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
  // A refused edge's facts and a refused step's preconditions, over empty
  // knowledges (their heap data is decoded below).
  { ...edge([0]), edgeFacts },
  // A handler's edge: past the continuation's, the thrown value first.
  { ...edge([0]), id: "edge:0:1", edgeIndex: 1, edgeFacts: { ...edgeFacts,
    requirement: { kind: "implication", test: 0, target: 1 } } },
  { ...edge([0]), edgeFacts: { ...edgeFacts, requirement: { kind: "input-value", slot: 0, input: 2 } } },
  { ...edge([0]), edgeFacts: { ...edgeFacts, requirement: { kind: "promised-input", slot: 0 } } },
  { ...common, kind: "node-typing", id: "r", source: node, sequent,
    postcondition: { facts: [{ fact: { int: { slot: 0 } }, entailed: false }, { fact: null, entailed: true }], known: emptyKnowledge } },
  { ...common, kind: "node-typing", id: "p", source: node, sequent,
    preconditions: { step: "call", known: emptyKnowledge, signatures: [{ requires: null,
      atoms: [{ fact: { index: { slot: 0 } }, entailed: false }, { fact: null, entailed: true }] }] } },
];
// Every kind of the union, so that a kind the reader does not decode fails
// below: a kind added to `ObligationDiagnostic` and not here fails to compile.
const kinds: { [K in ObligationDiagnostic["kind"]]: true } = {
  "node-typing": true, "edge-coverage": true, "expression-claim": true,
  "direct-obligation": true, "source-refusal": true, "production-failure": true,
};
for (const kind of Object.keys(kinds))
  assert.ok(cases.some((value) => value.kind === kind), `a case of kind ${kind}`);
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
// Each record's own diagnostic data, on its kind alone.
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  kind: "node-typing", id: "n", source: node, sequent, edgeFacts })}`), undefined);
// An edge's facts field by field: a field missing, an unknown field, a null
// knowledge, an unknown requirement.
const malformedEdgeFacts: Json[] = [
  { requirement: { kind: "facts" }, established: emptyKnowledge, lacking: emptyKnowledge },
  { requirement: { kind: "facts" }, established: emptyKnowledge, lacking: emptyKnowledge, known: emptyKnowledge, extra: 1 },
  { requirement: { kind: "facts" }, established: emptyKnowledge, lacking: null, known: emptyKnowledge },
  { requirement: { kind: "facts", test: 0 }, established: emptyKnowledge, lacking: emptyKnowledge, known: emptyKnowledge },
  { requirement: { kind: "other" }, established: emptyKnowledge, lacking: emptyKnowledge, known: emptyKnowledge },
];
for (const facts of malformedEdgeFacts)
  assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...edge([0]), edgeFacts: facts })}`), undefined,
    JSON.stringify(facts));
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common, kind: "node-typing", id: "r", source: node,
  sequent, postcondition: { facts: [], known: null } })}`), undefined);
assert.equal(readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...edge([0]),
  preconditions: { step: "call", known: emptyKnowledge, signatures: [] } })}`), undefined);
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

// The heap data as the verifier writes it: a fact's contents a set of values
// by kind, an elements fact's predicate the kinds it admits.
const contents = { nul: false, undef: false, tru: true, fls: false, sym: false, arr: false,
  num: { allBut: { xs: ["0"] } }, str: { these: { xs: ["checked"] } }, big: { these: { xs: [] } },
  obj: [[{ tag: "isStr", answer: true }]] };
const pred = { nul: false, undef: false, bool: false, num: true, str: true, big: false, sym: false, obj: false };
const heap = readDiagnostic(`obligation-diagnostic: ${JSON.stringify({ ...common,
  kind: "node-typing", id: "heap", sequent,
  source: { label: 0, sourceMap, node: null, claim: null,
    requiredKnowledge: {
      cells: [{ slot: 0, field: "id", contents }],
      values: [], links: [{ cell: 0, value: 1, alias: false, field: "id", optional: false },
        { cell: 0, value: 2, alias: false, field: { symbol: 3 }, optional: false }],
      separation: { depth: 2, facts: [{ slot: 0, fields: ["id"], partners: [[1, ["id", { symbol: 0 }]]] }] },
      elems: [{ slot: 1, pred, cond: null, negated: false }, { slot: 1, pred, cond: 0, negated: true }],
      indices: [{ fact: { bound: { array: 1, index: 2, strict: false } }, cond: null, negated: false },
        { fact: { index: { slot: 2 } }, cond: 0, negated: true }],
    } },
})}`);
assert.ok(heap?.kind === "node-typing");
const knowledge = heap.source.requiredKnowledge;
assert.deepEqual(knowledge?.cells[0].contents, { ...contents, num: { allBut: ["0"] }, str: { these: ["checked"] }, big: { these: [] },
  obj: [[{ tag: { kind: "isStr" }, answer: true }]] });
assert.deepEqual(knowledge?.separation.facts[0].partners, [[1, ["id", { symbol: 0 }]]]);
assert.deepEqual(knowledge?.elems, [{ slot: 1, pred: ["num", "str"], negated: false },
  { slot: 1, pred: ["num", "str"], cond: 0, negated: true }]);
assert.deepEqual(knowledge?.indices, [{ fact: { bound: { array: 1, index: 2, strict: false } }, negated: false },
  { fact: { index: { slot: 2 } }, cond: 0, negated: true }]);

console.log("Diagnostic decoder: all variants, heap data and malformed required fields");
