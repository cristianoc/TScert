/* First refusals of the supplied census of 043267592814 (2026-10-31).
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Site audit: session scratchpad, round/ranking.md. */
import {
  bullets, card, cards, code, cover, point, slide, stat, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

const measured = "Measured 2026-10-31 · census of 043267592814";

// These are observed source forms, not assertions of shared implementation defects.
const first: string[][] = [
  ["1", "Early use of capturedAt; outer arrow has no result annotation", "2,938", "1"],
  ["2", "Recursive parent walk checked at several signatures", "798", "6"],
  ["3", "Object.assign target read after argument-array destructuring", "792", "10"],
  ["4", "Scope spread overriding callbacks and a type alias’s source file", "780", "29"],
  ["5", "for-of over an indexed array with an empty-array fallback", "716", "26"],
  ["6", "Array literal spreading map results that build field records", "393", "2"],
  ["7", "Callback making a pair from a nested record spread", "352", "1"],
  ["8", "Name read on a computed declaration node", "311", "1"],
  ["9", "find callback calling a function stored in a graph field", "300", "1"],
  ["10", "map callback recursively printing type arguments", "293", "10"],
];
const more: string[][] = [
  ["11", "filter callback inside a function passed to flatMap", "229", "5"],
  ["12", "Spread of unknown after object and null tests", "200", "5"],
  ["13", "Two maps resolving declarations and serializing locations", "197", "1"],
  ["14", "Template interpolation after printing a nullable receiver field", "175", "5"],
  ["15", "Async record result may acquire a callable then", "129", "3"],
  ["16", "Callback returning a real path or null through a cache helper", "124", "9"],
  ["17", "Recursive visitor fails its stated effect bound", "120", "5"],
  ["18", "forEach through an optional object field after a test", "106", "1"],
  ["19", "Decoder asserts a writable result over checked input storage", "101", "1"],
  ["20", "node field read on a result selected by find", "100", "4"],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. This deck explains its first refusals when it checks the functions of its own source-reading code, in tools/. The census of 043267592814 measures 372 of 635 functions verified. The next two slides explain those terms. The ranking describes source constructs at the remaining functions’ first refusals, weighted by the statements they block.",
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
    label: measured, title: "372 of 635 functions verify", gap: 26,
    body: cards([
      stat("23.5%", "3,567 of 15,182 census statements belong to verified functions.", "ok"),
      stat("263", "functions are refused: 223 at search or checking, 40 at source or proposal restrictions."),
      stat("0", "stage timeouts, with a limit of 300 seconds per process stage."),
    ]) + bullets([
      point("A slice", "a copy of one top-level function and its dependencies, run through the pipeline. A refusal can occur in a dependency retained in the copy."),
      point("The weight", "each refused function contributes its own statements once, to its first refusal: 11,615 blocked statements. Statements include returns, assignments and tests. Later refusals are outside this measurement."),
      point("The source", "the supplied census-tools-043267592814 record and refusals.json. This is the ordinary census. The earlier deck’s diagnostic census continued past refusals under assumptions and measured something different."),
    ]),
  }),
  slide("method", {
    label: measured, title: "One search-failure message contains many source forms", gap: 24,
    body: table(["The record’s group", "Statements", "Functions", "What the source shows"], [
      ["Source expression obligation", "3,803", "142", "Argument reads, spreads, loops, calls, templates and other forms"],
      ["Source direct obligation", "946", "13", "Several different callbacks"],
      ["Closure expression claim", "701", "24", "Recursive maps, assertions and other closure results"],
      ["Arrow claims do not match their bodies", "379", "1", "collect in declaration-graph.mts; no location in the record"],
    ], [28, 12, 12, 48]) + bullets([
      point("Confirmed from source", "each located refusal is read in its supplied slice. Generic groups are split by refused expression and the functions reaching it. A shared expression confirms a source form; the exact failed proof may require investigation."),
      point("A separate investigation", "the unlocated 379-statement mismatch is outside the construct ranking: collect contains several callbacks. The message does not establish which one fails."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten heaviest observed constructs", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], first, [5, 69, 14, 12], { compact: true }) + bullets([
      "Counts measure blocked code, not code guaranteed to verify when this refusal is removed. These ten sites have no exact refusal case identified in pipeline/cases.mts. The following slides show the heaviest sites and distinguish related cases.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Constructs 11–20", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], more, [5, 69, 14, 12], { compact: true }) + bullets([
      "Construct 15 needs a guarantee that neither the record nor its prototype can acquire a callable then during its lifetime: promise resolution may invoke that method. invalid-async-object is a related negative case. An effect bound states how calls may change locations. Construct 19’s storage issue is explained on “A decoder’s checked contents and its storage”. Other rows have no exact case identified.",
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
      point("Cases", "blocker-every-mixed-closure shows a related signature-dependent translation: one closure becomes different programs at different parameter types. No exact case is identified for these four sites. A small source with the same refusal is needed before asserting a shared cause."),
    ]),
  }),
  slide("round", {
    label: "Each case is paired with the census functions it targets · cases.mts and WORK.md", title: "Five positive cases and the census sites beyond them", gap: 18,
    body: '<div style="width:1656px">' + table(["Positive case", "What it checks", "First refusal in this record"], [
      ["blocker-census-options-default", "Optional fields retain their annotated type through an empty-object default", "collectDeclarations: early capturedAt binding"],
      ["blocker-census-rest-result", "A closure collecting rest arguments has an inferred result", "lowerFile and five callers: recursive parent walk"],
      ["blocker-flat-map-narrow-field", "A fresh array’s allocation states which element types may be written to it", "expr and nine other functions: Object.assign target read"],
      ["blocker-census-set-copy", "Copying optional built-in Sets retains the element type", "29 functions: scope spread overriding callbacks"],
      ["blocker-census-import-guard-call", "An exact-kind test selects ordinary import nodes", "Statement slices: loop in functionPlacement"],
    ], [31, 37, 32], { compact: true }) + '</div>' + bullets([
      point("The same-function comparison", "WORK.md compares f502699ca098 and 043267592814: 372 of 635 verified in each, zero functions gained or lost. Seventeen first-refusal messages differ. A case’s positive outcome does not imply its whole census function verifies."),
    ]),
  }),
  slide("storage", {
    label: "Construct 19 · 101 statements, 1 function", title: "A decoder’s checked contents and its storage", gap: 22,
    body: code([
      "// decodeFlowDocument checks parsed JSON, then closes with:",
      "const document: unknown = value;",
      "return document as FlowDocument;",
    ]) + bullets([
      point("The names", "a decoder checks input and returns a typed value. FlowDocument describes TScert’s graph of execution steps. value is the parsed input; document aliases its storage. unknown supplies no shape, and as asserts the result type."),
      point("The obligation", "checks of current contents alone do not establish the contracts of writable arrays and fields. A different reference may write values the asserted result type excludes. The record refuses the closing assertion."),
      point("Repair site", "source-flow.mts, decodeFlowDocument, closing assertion. SOURCE-REWRITES.md, “A decoder’s result asserted over parsed storage”, gives the repair: build fresh storage from checked fields. A stronger annotation alone does not establish it. invalid-decoder-closing-assertion demonstrates the related aliasing problem."),
    ]),
  }),
  slide("routes", {
    label: "How a refusal is answered · SOURCE-REWRITES.md", title: "The first route that establishes the obligation at acceptable cost", gap: 20,
    body: table(["Route", "What the route requires"], [
      ["1. Support", "A rule or external contract admits the construct"],
      ["2. A runtime check", "An executable check establishes the whole property"],
      ["3. A repair", "The source corrects a defect the refusal reveals"],
      ["4. Avoidance", "An equivalent source form avoids costly support"],
      ["5. A host boundary", "An external service’s operation has no model. Only values made by that service meet the small module’s signatures. Callers use its audited contract and effects; the module stays refused"],
      ["6. A trusted unit", "Local code is exempt from checking, with the owner accepting its full contract as an assumption"],
      ["7. A proof", "A Lean proof establishes the needed fact in the model"],
      ["8. The refusal stays", "No route establishes the obligation at acceptable cost"],
    ], [25, 75]) + bullets([
      "Before choosing a route, check whether TScert’s source discards information it already checked. A decoder’s closing assertion also needs scrutiny of storage contracts. This ranking identifies sites and evidence limits; a route requires its own justification.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and scope", title: "First refusals in one fixed record", gap: 24,
    body: bullets([
      point("Measured", "census-tools-043267592814-2026-10-31T04-18-35-953Z.json in the supplied census directory 2db902ca8b7b: clean commit 043267592814, tools/, 300-second stage limit. Counts come from function outcomes and the statement inventory."),
      point("Inspected", "refusals.json and tools/tools/slice-*.mts in that directory. Each refusal matches the record. Source spans count UTF-16 code units, as TypeScript does. The session’s round/ranking.md lists all sites, weights, case matches and repair assessments."),
      point("Source policy", "pipeline/cases.mts owns case expectations. WORK.md owns the census comparison. SOURCE-REWRITES.md owns the routes and decoder storage repair. No new pipeline run supplies a number in this deck."),
      point("Limits", "Observed source forms are confirmed. Generic search failures leave the exact failed obligation to isolate. Later refusals and future gains are unmeasured. The 379-statement unlocated arrow mismatch is a separate investigation."),
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
