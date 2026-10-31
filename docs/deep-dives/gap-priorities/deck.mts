/* First refusals of the supplied census of 340214a96fca (2026-10-31).
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Site audit: session scratchpad, round/ranking.md. */
import {
  bullets, card, cards, code, cover, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

const measured = "Measured 2026-10-31 · census of 340214a96fca";

// These are observed source forms, not assertions of shared implementation defects.
const first: string[][] = [
  ["1", "Early use of capturedAt; outer arrow has no result annotation", "2,938", "1"],
  ["2", "Recursive parent walk checked at several signatures", "798", "6"],
  ["3", "Object.assign target read after argument-array destructuring", "792", "10"],
  ["4", "Scope spread overriding callbacks and a type alias’s source file", "780", "29"],
  ["5", "for-of over an indexed array with an empty-array fallback", "716", "26"],
  ["6", "Call finding the first optional constructor parameter inside map", "393", "2"],
  ["7", "map callback replacing native method types with unknown", "379", "1"],
  ["8", "map callback allocating a generic signature’s type-parameter record", "352", "1"],
  ["9", "initializer read after an in test on a compiler node’s parent", "313", "1"],
  ["10", "find callback calling a function stored in a graph field", "300", "1"],
];
const more: string[][] = [
  ["11", "filter callback inside a function passed to flatMap", "229", "5"],
  ["12", "Spread of unknown after object and null tests", "200", "5"],
  ["13", "Two maps resolving declarations and serializing locations", "197", "1"],
  ["14", "Captured array read before flatMap calls each element’s function", "187", "6"],
  ["15", "Template interpolation after printing a nullable receiver field", "175", "5"],
  ["16", "Async record result may acquire a callable then", "129", "3"],
  ["17", "Cache callback returning a record whose answer is a real path or null", "124", "9"],
  ["18", "Recursive visitor fails its stated effect bound", "120", "5"],
  ["19", "JSON.stringify of a field key after string and symbol tests", "106", "4"],
  ["20", "forEach through an optional object field after a test", "106", "1"],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. This deck explains its first refusals when it checks the functions of its own source-reading code, in tools/. The census of 340214a96fca measures 370 of 635 functions verified. The next two slides explain those terms. The ranking describes source constructs at the remaining functions’ first refusals, weighted by the statements they block.",
  }),
  slide("terms", {
    label: "How to read the result", title: "A checked function, a refusal, and a small case", gap: 26,
    body: cards([
      card("Verified and refused", "The parser reads source and annotations. The producer proposes type claims. A proof search tries to justify them, and a checker validates the evidence. A function is verified when this whole path succeeds. A refusal names an unsupported source form or an obligation the proposed evidence cannot establish."),
      card("The safety boundary", "The checker’s type-safety result is proved in Lean, a proof assistant. Applying it to source also relies on faithful parsing and contracts: descriptions of external code taken as assumptions. A failed search alone establishes neither a source bug nor an unsafe program."),
      card("A case", "A small TypeScript file has an expected outcome in pipeline/cases.mts. A positive case must verify. A negative case must be refused. A gap case records a missing capability. An exact case reproduces the census construct and its refusal. A related case shows only part of it."),
    ]),
  }),
  slide("find", {
    label: measured, title: "370 of 635 functions verify", gap: 26,
    body: cards([
      stat("23.3%", "3,545 of 15,184 census statements belong to verified functions.", "ok"),
      stat("265", "functions are refused: 232 at search or checking, 33 at source or proposal restrictions."),
      stat("0", "stage timeouts, with a limit of 300 seconds per process stage."),
    ]) + bullets([
      point("A slice", "a copy of one top-level function and its dependencies, run through the pipeline. A refusal can occur in a dependency retained in the copy."),
      point("The weight", "each refused function contributes its own statements once, to its first refusal: 11,639 blocked statements. Statements include returns, assignments and tests. Later refusals are outside this measurement."),
      point("The source", "the supplied census-tools-340214a96fca record and refusals.json. This ordinary census stops at each function’s first refusal. The comparison with the preceding ordinary census appears on “Cases and the functions they target”."),
    ]),
  }),
  slide("method", {
    label: measured, title: "One search-failure message contains many source forms", gap: 24,
    body: table(["The record’s group", "Statements", "Functions", "What proof is missing"], [
      ["Source expression obligation", "4,333", "154", "That an expression meets its claimed type, using the known types and facts"],
      ["Source direct obligation", "973", "13", "That one type is included in another; here, that each proposed callback signature fits its source annotation"],
      ["Closure expression claim", "578", "19", "That an expression inside a closure meets its claimed type under that closure’s parameters and captured values"],
      ["Incoming edge obligation", "331", "12", "That an execution step establishes the type claims required at its destination"],
      ["Effect refusal", "319", "14", "That the body obeys its proposed limits on changes to stored values"],
    ], [28, 12, 12, 48]) + bullets([
      point("Confirmed from source", "each located refusal is read in its supplied slice. Generic groups are split by refused expression and the functions reaching it. A shared expression confirms a source form; the exact failed proof may require investigation."),
      point("Scope", "the ranking names observed constructs. A generic search failure does not identify a shared implementation defect or establish that the source is unsafe."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten heaviest observed constructs", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], first, [5, 69, 14, 12], { compact: true }) + bullets([
      "Counts measure blocked code, not code guaranteed to verify when this refusal is removed. No exact case for these current refusals is identified in pipeline/cases.mts. The following slides show the heaviest sites and distinguish related cases.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Constructs 11–20", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], more, [5, 69, 14, 12], { compact: true }) + bullets([
      "Construct 16 needs a guarantee that neither the record nor its prototype can acquire a callable then during its lifetime: promise resolution may invoke that method. invalid-async-object is a related negative case. An effect bound states how calls may change locations. Construct 21’s storage issue is explained on “A decoder’s checked contents and its storage”. JSON.stringify serializes a value to JSON text. Other rows have no exact case identified.",
    ]),
  }),
  slide("early-binding", {
    label: "Construct 1 · 2,938 statements, 1 function", title: "A closure mentions capturedAt before its declaration", gap: 22,
    body: code([
      "// Declaration in collectDeclarations; earlier closures mention capturedAt.",
      "const capturedAt = (use: Node, what: string) =>",
      "  (parameter: ts.TypeParameterDeclaration): TypeTerm => {",
      "    // Check name resolution, then represent the type parameter.",
      "    …",
      "  };",
    ]) + bullets([
      point("The names", "Node is a TypeScript compiler node. TypeParameterDeclaration describes a declared type parameter. TypeTerm represents a type. use is the use site, what labels an error, and parameter is the captured type parameter."),
      point("The refusal", "the binding may be read before initialization and needs its type stated. The inner arrow states TypeTerm; the outer arrow has no result annotation. This confirms the source construct. It does not establish an actual read of an uninitialized value."),
      point("Case and route", "no exact case. function-declaration-before-initialization is related. An annotation is a candidate source change whose evidence needs checking. No previously checked shape is discarded here."),
    ]),
    note: "Source: slice-declaration-graph-collectDeclarations.mts, declaration at line 2248",
  }),
  slide("later-sites", {
    label: "Constructs 2–5 · inspected in the supplied slices", title: "The first refusal reaches another construct", gap: 20,
    body: table(["Construct and site", "Recorded refusal", "What the source establishes"], [
      ["2. lowerFile: topStatement, a walk to a containing statement", "Closure body translates to different programs at its signatures", "The arrow follows a node’s parent; the differing operation needs investigation"],
      ["3. expr: gate.expr(target) in the Object.assign branch", "Source expression obligation", "Argument count is checked, then the array is destructured; target goes to the expression reader"],
      ["4. readTypeTerm: scope spread", "Source expression obligation", "The literal overrides a type alias’s source file and callbacks; the failed member is unestablished"],
      ["5. functionPlacement: for-of over mentions[i] ?? []", "Source expression obligation", "An indexed array or a fresh empty array supplies the loop’s values"],
    ], [32, 25, 43]) + bullets([
      point("Two signatures in a related case", "In blocker-every-mixed-closure, a boolean callback calls node.getSourceFile(). Its written parameter accepts a compiler node or a record holding that function. Passing it to every on an array of compiler nodes also asks for a signature accepting just those nodes."),
      point("Two translations of that call", "At the written signature: read and call getSourceFile on the object in one step. At every’s signature: obtain the compiler method with node saved as its receiver, then call it. These are different sequences of model operations. One closure needs the same program at both signatures."),
      point("Scope", "This explains the message using the related case. The parent walk’s differing operation is unestablished; none of these four sites has an exact case."),
    ]),
  }),
  slide("round", {
    label: "Cited case expectations · pipeline/cases.mts; measured census comparison · WORK.md", title: "Cases and the functions they target", gap: 18,
    body: table(["Positive case", "What it checks", "Current first refusal in its census functions"], [
      [`blocker-census-spread-map-records ${status("ok", "positive")}`, "Spreading mapped records into an array", "classBody and classStmt: firstOptional(all), finding the first optional constructor parameter"],
      [`blocker-census-annotated-node-union ${status("ok", "positive")}`, "An annotated callback over compiler member arrays", "collect: a proposed callback signature fails its source annotation in nativeFields.map"],
      [`blocker-census-spread-nested-field ${status("ok", "positive")}`, "Nested spreads over stated JSON data", "selectGlobal: allocating a type-parameter record for a generic signature"],
      [`invalid-in-union-read ${status("ok", "positive")}`, "A union arm states an absent spread field", "fragment-parts.mapExprParts and its callers: source-expression obligation"],
      [`blocker-census-effect-map-result ${status("ok", "positive")}`, "A map callback followed by array join", "Four claim-text functions: JSON.stringify(key), serializing a field key"],
    ], [31, 30, 39], { compact: true }) + bullets([
      point("Measured comparison", "043267592814 → 340214a96fca: 372 → 370 of 635 functions verified; 3,567 → 3,545 verified statements. Gained: files.treeDigest. Lost: computed-types.parameterMembers (method next read off its object), unchecked.unstated and unchecked.boundary (incoming edge obligations). These names identify functions in the corresponding tools/ files."),
      point("Scope", "All five cases above have positive expectations; even the name invalid-in-union-read names a positive case. A case’s success does not establish its whole census function. The separate blocker-census-nested-field-json case retains a gap for serializing open nested records."),
    ]),
  }),
  slide("storage", {
    label: "Construct 21 · 101 statements, 1 function", title: "A decoder’s checked contents and its storage", gap: 22,
    body: code([
      "// decodeFlowDocument checks parsed JSON, then closes with:",
      "const document: unknown = value;",
      "return document as FlowDocument;",
    ]) + bullets([
      point("The names", "a decoder checks input and returns a typed value. FlowDocument describes TScert’s graph of execution steps. value is the parsed input; document aliases its storage. unknown supplies no shape, and as asserts the result type."),
      point("The obligation", "checks of current contents alone do not establish the contracts of writable arrays and fields. A different reference may write values the asserted result type excludes. The record refuses the closing assertion."),
      point("Repair site", "source-flow.mts, decodeFlowDocument, closing assertion. SOURCE-REWRITES.md, “A decoder’s result asserted over parsed storage”, describes the related repair pattern: build fresh storage from checked fields. A stronger annotation alone does not establish it. invalid-decoder-closing-assertion demonstrates the related aliasing problem."),
    ]),
  }),
  slide("routes", {
    label: "How a refusal is answered · SOURCE-REWRITES.md", title: "The first route that establishes the obligation at acceptable cost", gap: 20,
    body: table(["Route", "What the route requires"], [
      ["1. Support", "A rule or external contract admits the construct"],
      ["2. A runtime check", "An executable check establishes the whole property"],
      ["3. A repair", "The source corrects a defect the refusal reveals"],
      ["4. Avoidance", "An equivalent source form avoids costly support"],
      ["5. A host boundary", "A small wrapper module performs an external service operation with no model. Its signatures admit only that service’s values. Its functions stay refused; callers assume its audited result and effect contract"],
      ["6. A trusted unit", "Local code is exempt from checking, with the owner accepting its full contract as an assumption"],
      ["7. A proof", "A Lean proof establishes the needed fact in the model"],
      ["8. The refusal stays", "No route establishes the obligation at acceptable cost"],
    ], [25, 75], { compact: true }) + bullets([
      point("Example of route 5", "tools/client-prototype.mts wraps the compiler client’s request methods, reached through its prototype. Only the compiler package can make its API input. Callers assume the wrapper returns the service’s answer or throws, with the stated effects. The wrapper and service remain outside the proof."),
      "Before choosing a route, check for discarded type information and for assertions over storage whose writes the checks do not constrain.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and scope", title: "First refusals in one fixed record", gap: 24,
    body: bullets([
      point("Measured", "census-tools-340214a96fca-2026-10-31T07-12-06-447Z.json in the supplied census directory 2db902ca8b7b: clean commit 340214a96fca, tools/, 300-second stage limit. Counts come from function outcomes and the statement inventory."),
      point("Inspected", "The session’s work/refusals.json lists the refusals; tools/tools/slice-*.mts is in the cited census directory. Each refusal matches the record. Source spans count UTF-16 code units, as TypeScript does. The session’s work/round/ranking.md lists all sites, weights, case matches and repair assessments."),
      point("Source policy", "pipeline/cases.mts owns case expectations. WORK.md owns the census comparison. SOURCE-REWRITES.md owns the routes and decoder storage repair. No new pipeline run supplies a number in this deck."),
      point("Limits", "Observed source forms are confirmed. Generic search failures leave the exact failed obligation to isolate. Later refusals and future gains are unmeasured. A function can meet further obligations beyond the first one this record reports."),
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert’s proofs fail",
  slides,
  sections: [
    { description: "The census and how first refusals become a ranking.", start: "cover" },
    { description: "The heaviest observed constructs and their evidence.", start: "priority" },
    { description: "Case outcomes, repair sites and routes for a refusal.", start: "round" },
  ],
};
export default deck;
