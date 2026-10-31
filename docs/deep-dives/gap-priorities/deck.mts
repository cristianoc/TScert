/* First refusals of the supplied census of 13d2104e09a9 (2026-10-31).
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Site audit: session scratchpad, round/ranking.md. */
import {
  bullets, card, cards, code, cover, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

const measured = "Measured 2026-10-31 · census of 13d2104e09a9";

// These are observed source forms, not assertions of shared implementation defects.
const first: string[][] = [
  ["1", "Identifier text read after resolving interface bases", "2,941", "1"],
  ["2", "Parameter read through a tested optional promise field", "942", "45"],
  ["3", "Reassigned translated-functions array read before filter", "798", "6"],
  ["4", "Callable initialization returned as a withValue record", "794", "10"],
  ["5", "Map keys iterator spread into an array", "681", "25"],
  ["6", "Base-prototype identifier record on a conditional branch", "393", "2"],
  ["7", "Mapped member array read before testing optional fields", "382", "1"],
  ["8", "Method overload forms called inside flatMap", "356", "1"],
  ["9", "Decoded promise assigned through conditional nested records", "321", "2"],
  ["10", "Array length returned as a filter callback result", "313", "1"],
];
const more: string[][] = [
  ["11", "Sorted and mapped result array read before push", "300", "1"],
  ["12", "Primitive JSON value converted with String", "294", "10"],
  ["13", "Named record used where an index signature is required", "248", "8"],
  ["14", "Compiler node end position read after testing for a previous match", "206", "2"],
  ["15", "Parameter-string map reads a required-parameter count", "175", "5"],
  ["16", "Map entries iterator spread for canonicalization", "116", "1"],
  ["17", "Mapped directory-entry pairs serialized as JSON", "111", "9"],
  ["18", "Optional dictionary lookup at a possibly inherited key", "109", "3"],
  ["19", "Decoded diagnostic assembled through an unknown-valued record", "109", "1"],
  ["20", "Parsed flow document asserted as a writable graph", "101", "1"],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. This deck explains its first refusals when it checks the functions of its own source-reading code, in tools/. The census of 13d2104e09a9 measures 369 of 637 functions verified. The next two slides explain those terms. The ranking describes source constructs at the remaining functions’ first refusals, weighted by the statements they block.",
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
    label: measured, title: "369 of 637 functions verify", gap: 26,
    body: cards([
      stat("22.4%", "3,402 of 15,206 census statements belong to verified functions.", "ok"),
      stat("268", "functions are refused: 192 at search, 76 at source or proposal restrictions."),
      stat("0", "stage timeouts, with a limit of 300 seconds per process stage."),
    ]) + bullets([
      point("A slice", "a copy of one top-level function and its dependencies, run through the pipeline. A refusal can occur in a dependency retained in the copy."),
      point("The weight", "each refused function contributes its own statements once, to its first refusal: 11,804 blocked statements. Statements include returns, assignments and tests. Later refusals are outside this measurement."),
      point("The source", "the supplied census-tools-13d2104e09a9 record and refusals.json. This ordinary census stops at each function’s first refusal. The comparison with the preceding ordinary census appears on “Cases and the functions they target”."),
    ]),
  }),
  slide("method", {
    label: measured, title: "One search-failure message contains many source forms", gap: 24,
    body: table(["The record’s group", "Statements", "Functions", "What proof is missing"], [
      ["Source expression obligation", "3,757", "126", "That an expression meets its claimed type, using the known types and facts"],
      ["Missing field text", "2,941", "1", "The producer cannot read text from the proposed type of an interface base expression"],
      ["Closure expression claim", "1,825", "22", "That an expression inside a closure meets its claimed type under that closure’s parameters and captured values"],
      ["Optional object field read", "942", "45", "The producer refuses a nested read through a field whose object-or-undefined contract its test does not narrow"],
      ["Incoming edge obligation", "695", "12", "That an execution step establishes the type claims required at its destination"],
    ], [28, 12, 12, 48]) + bullets([
      point("Confirmed from source", "each located refusal is read in its supplied slice. Generic groups are split by refused expression and the functions reaching it. A shared expression confirms a source form; the exact failed proof may require investigation."),
      point("Scope", "these are the five heaviest unsplit messages. The next slides rank source constructs. A generic search failure does not identify a shared implementation defect or establish that the source is unsafe."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten heaviest observed constructs", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], first, [5, 69, 14, 12], { compact: true }) + bullets([
      "A promise describes what a guard or assertion function establishes about a parameter. Row 2 reads its parameter number through an optional field; “Optional fields and further obligations” explains it and rows 3–5 and 9. Row 6 allocates a record describing a read of the base class’s prototype. Rows 7–8 concern member collection and overload reading. Row 10 returns a length as a truthy filter result. Counts measure blocked code; further refusals may follow.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Constructs 11–20", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], more, [5, 69, 14, 12], { compact: true }) + bullets([
      "An index signature constrains every key of its kind. Row 13 has the gap case named-implicit-index; its record gives no source position. Canonicalization serializes contracts for comparison, omitting source positions. Row 18 has the negative case index-signature. Rows 19 and 20 are explained on “Decoders and checked storage”. Row 11 reads the result array in familyTable, which collects descriptions of compiler node types. These twenty rows cover 9,690 statements in 135 functions.",
    ]),
  }),
  slide("early-binding", {
    label: "Construct 1 · measured 2,941 statements, 1 function", title: "A tested interface base is read again after calls", gap: 22,
    body: code([
      "if (!ts.isIdentifier(base.expression) || base.typeArguments?.length)",
      "  throw Error(…);",
      "const targets = (targetOf(checker, base.expression)?.declarations ?? [])",
      "  .map(x => x.resolve());",
      "const [only] = targets;",
      "if (!only || targets.length !== 1 || !ts.isInterfaceDeclaration(only))",
      "  throw Error(`the base ${base.expression.text} of ${d.name.text} is not one interface`);",
    ]) + bullets([
      point("The names", "In collectDeclarations, d is an interface declaration and base is one of its bases. ts is the TypeScript compiler API. isIdentifier tests for a name with text; typeArguments lists generic arguments. targetOf uses checker to find declarations, and resolve obtains each declaration. only is the sole target when one exists. The ellipsis omits the first error’s text."),
      point("Measured refusal", "the producer reports missing field text at base.expression.text in the error message. The source tests that expression before resolving declarations, then reads it again. This observation does not establish which call or claim loses the fact."),
      point("Case and repair assessment", "invalid-path-witness-call is related: a call can invalidate a tested field path. No exact case for this base walk is identified. No explicit conversion of a checked shape to unknown occurs here."),
    ]),
    note: "Source: slice-declaration-graph-collectDeclarations.mts:969–975; excerpt wraps the targets declaration",
  }),
  slide("later-sites", {
    label: "Constructs 2–5 and 9 · cited sites; measured weights on the ranking", title: "Optional fields and further obligations", gap: 20,
    body: table(["Construct and site", "Recorded refusal", "What the source establishes"], [
      ["2. guardOf, promiseText, samePromise", "Producer refuses param through an optional object field; no recorded span", "Candidate reads test a guard or assertion promise, then read its parameter number. These helpers extract, print or compare promises; dependencies carry them into 45 slices"],
      ["3. lowerFile: lowered.filter", "Closure expression claim at the array before filter", "The array holds translated declarations; a loop reassigns it after filtering references to omitted functions"],
      ["4. expr: callable initialization", "Expression claim at the returned withValue record", "The record carries a function, its initial fields and both types; the destructured target check is passed"],
      ["5. hoisting: Map keys spread", "Expression claim at the iterator spread", "Declaration placement keys are copied into an array in insertion order"],
      ["9. decodeCallEffect: promise assignment", "Storage-contract claim at conditional nested records", "A decoder checks the parameter number, then allocates a guard or assertion promise. A storage contract constrains future assignments"],
    ], [27, 29, 44], { compact: true }) + bullets([
      "Names: lowerFile translates a file; expr reads an expression; hoisting arranges early-bound declarations. withValue is the translated callable-initialization record. No exact case is identified for these five refusals. The small positive cases on the next slide establish earlier obligations. The generic search messages leave the exact failed proof to isolate.",
    ]),
  }),
  slide("round", {
    label: "Cited case expectations · pipeline/cases.mts; measured census comparison · WORK.md", title: "Cases and the functions they target", gap: 10,
    body: table(["Positive case (blocker-gap-round- prefix)", "What it checks", "First refusal in its census functions"], [
      [`early-capture ${status("ok", "positive")}`, "An outer arrow states its returned function type", "collectDeclarations: missing text in an interface base expression"],
      [`parent-walk ${status("ok", "positive")}`, "Recursive callbacks retain their declared parameters", "lowerFile and callers: lowered array read before filter"],
      [`assign-target ${status("ok", "positive")}`, "A destructured target is checked for undefined", "expr and callers: returned callable-initialization record"],
      [`scope-spread ${status("ok", "positive")}`, "A type-reading context record states the function fields it copies", "readTypeTerm and callers: param read through an optional promise field"],
      [`indexed-for-of ${status("ok", "positive")}`, "Iteration over an indexed value or an empty array", "functionPlacement verifies; hoisting and callers reach a Map keys spread"],
    ], [29, 31, 40], { compact: true }) + bullets([
      point("Measured comparison", "f3434c21ffc7 → 13d2104e09a9: 382/637 → 369/637 verified functions; 3,754/15,202 → 3,402/15,206 verified statements. No gains; 13 losses: nine printing helpers in named-record, sameEffect and samePromise in type-term, and decodeCallEffect and decodeGraph in type-graph. The first eleven reach the optional promise-field refusal; the two decoders reach the conditional promise assignment. WORK.md lists every function."),
      point("Scope", "case expectations concern small sources. The optional-parameter helper is positive. The unrestricted captured-arms reduction is negative; its store-preserving variant is positive. The reduction case’s six functions first refuse conversion of a JSON primitive to text. Store-preserving means preserving existing stored values’ contracts. Case success does not establish a whole census function."),
    ]),
  }),
  slide("storage", {
    label: "Constructs 19 and 20 · measured 109 and 101 statements", title: "Decoders and checked storage", gap: 22,
    body: code([
      "// readDiagnostic assembles decoded fields through this dictionary:",
      "const result: { [key: string]: unknown } = { ...d };",
      "// Later it assigns decoded parts, then asserts the diagnostic type.",
      "return result as unknown as ObligationDiagnostic;",
      "// decodeFlowDocument checks value, then aliases its storage:",
      "const document: unknown = value;",
      "return document as FlowDocument;",
    ]) + bullets([
      point("The names", "a decoder checks input and returns a typed value. d and value are parsed JSON values. ObligationDiagnostic describes a failed proof obligation; FlowDocument describes a graph of execution steps. unknown gives no shape; as asserts a type."),
      point("Repair sites", "diagnostic.mts#readDiagnostic stores typed decoded parts in an unknown-valued dictionary. source-flow.mts#decodeFlowDocument asserts a writable graph over checked parsed storage. A test of present contents alone does not constrain future writes through other references. Both closing assertions are refused."),
      point("Cited repair pattern", "SOURCE-REWRITES.md, “A decoder’s result asserted over parsed storage”: build fresh typed storage from checked fields. invalid-decoder-closing-assertion demonstrates the related aliasing problem. Applying that pattern to these full decoders needs validation; the record alone does not prove the exact cause of either failed search."),
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
    ], [25, 75], { compact: true }) + bullets([
      point("Effect", "a contract may bound how a call changes stored values. A host boundary’s result and effect are assumptions about its code."),
      "Before choosing a route, check for discarded type information and for assertions over storage whose writes the checks do not constrain. Construct 13’s record-to-index refusal protects keys its named fields do not describe; construct 18’s lookup may find inherited methods.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and scope", title: "First refusals in one fixed record", gap: 24,
    body: bullets([
      point("Measured", "census-tools-13d2104e09a9-2026-10-31T18-47-44-590Z.json in the supplied census directory 2db902ca8b7b: clean commit 13d2104e09a9, tools/, 300-second stage limit. Counts come from function outcomes and the statement inventory."),
      point("Inspected", "The session’s work/refusals.json lists the refusals; tools/tools/slice-*.mts is in the cited census directory. All 268 details match the record; every refused slice matches its recorded source hash. Source spans count UTF-16 code units, as TypeScript does. work/round/ranking.md lists every site, its weight, the top twenty case comparisons and repair assessments."),
      point("Source policy", "pipeline/cases.mts owns case expectations. WORK.md owns the census comparison. SOURCE-REWRITES.md owns the routes and decoder storage repair. No new pipeline run supplies a number in this deck."),
      point("Revision marks", "the marked page compares with deck commit f893d8b4, the base named in the intervening deck records. This is separate from the ordinary census comparison on “Cases and the functions they target”."),
      point("Limits", "Observed source forms are confirmed. Generic search failures leave the exact failed obligation to isolate. Later refusals and future gains are unmeasured. Constructs 2 and 13 name restrictions without a recorded source span; candidate reads for construct 2 are inspected, not assigned exact refusal locations."),
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
