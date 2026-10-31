/* First refusals of the supplied census of aa376e0a92d8 (2026-10-31).
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Site audit: session scratchpad, round/ranking.md. */
import {
  bullets, card, cards, code, cover, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

const measured = "Measured 2026-10-31 · census of aa376e0a92d8";

// These are observed source forms, not assertions of shared implementation defects.
const first: string[][] = [
  ["1", "Identifier text read after resolving interface bases", "2,941", "1"],
  ["2", "Reassigned translated-functions array read before filter", "798", "6"],
  ["3", "Callable initialization returned as a withValue record", "794", "10"],
  ["4", "Generic function type passed to quantified", "780", "29"],
  ["5", "Map keys iterator spread into an array", "681", "25"],
  ["6", "First optional constructor parameter found inside map", "393", "2"],
  ["7", "Mapped member array read before testing optional fields", "382", "1"],
  ["8", "Method overload forms called inside flatMap", "352", "1"],
  ["9", "Array length returned as a filter callback result", "313", "1"],
  ["10", "Sorted and mapped result array read before push", "300", "1"],
];
const more: string[][] = [
  ["11", "Named record used where an index signature is required", "248", "8"],
  ["12", "Compiler node’s end position read after testing for a previous match", "206", "2"],
  ["13", "Mapped arms array read before reduction", "187", "6"],
  ["14", "Parameter-string map reads a required-parameter count", "175", "5"],
  ["15", "Map entries iterator spread for canonicalization", "116", "1"],
  ["16", "Mapped directory-entry pairs serialized as JSON", "111", "9"],
  ["17", "Optional dictionary lookup at a possibly inherited key", "109", "3"],
  ["18", "Decoded diagnostic assembled through an unknown-valued record", "109", "1"],
  ["19", "Primitive JSON value converted with String", "106", "4"],
  ["20", "Parsed flow document asserted as a writable graph", "101", "1"],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. This deck explains its first refusals when it checks the functions of its own source-reading code, in tools/. The census of aa376e0a92d8 measures 382 of 637 functions verified. The next two slides explain those terms. The ranking describes source constructs at the remaining functions’ first refusals, weighted by the statements they block.",
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
    label: measured, title: "382 of 637 functions verify", gap: 26,
    body: cards([
      stat("24.7%", "3,754 of 15,201 census statements belong to verified functions.", "ok"),
      stat("255", "functions are refused: 224 at search, 31 at source or proposal restrictions."),
      stat("0", "stage timeouts, with a limit of 300 seconds per process stage."),
    ]) + bullets([
      point("A slice", "a copy of one top-level function and its dependencies, run through the pipeline. A refusal can occur in a dependency retained in the copy."),
      point("The weight", "each refused function contributes its own statements once, to its first refusal: 11,447 blocked statements. Statements include returns, assignments and tests. Later refusals are outside this measurement."),
      point("The source", "the supplied census-tools-aa376e0a92d8 record and refusals.json. This ordinary census stops at each function’s first refusal. The comparison with the preceding ordinary census appears on “Cases and the functions they target”."),
    ]),
  }),
  slide("method", {
    label: measured, title: "One search-failure message contains many source forms", gap: 24,
    body: table(["The record’s group", "Statements", "Functions", "What proof is missing"], [
      ["Source expression obligation", "4,471", "151", "That an expression meets its claimed type, using the known types and facts"],
      ["Missing field text", "2,941", "1", "The producer cannot read text from the proposed type of an interface base expression"],
      ["Closure expression claim", "2,012", "28", "That an expression inside a closure meets its claimed type under that closure’s parameters and captured values"],
      ["Source direct obligation", "378", "7", "That a proposed callback signature fits its source annotation"],
      ["Incoming edge obligation", "302", "10", "That an execution step establishes the type claims required at its destination"],
    ], [28, 12, 12, 48]) + bullets([
      point("Confirmed from source", "each located refusal is read in its supplied slice. Generic groups are split by refused expression and the functions reaching it. A shared expression confirms a source form; the exact failed proof may require investigation."),
      point("Scope", "these are the five heaviest unsplit messages. The next slides rank source constructs. A generic search failure does not identify a shared implementation defect or establish that the source is unsafe."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten heaviest observed constructs", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], first, [5, 69, 14, 12], { compact: true }) + bullets([
      "Names: lowered holds translated functions; withValue describes a function with initial fields; quantified reads a generic function type. Rows 1–5 are explained next. Row 6 has the gap case blocker-gap-round-optional-parameter. Other rows have no exact case identified. Counts measure blocked code; further refusals may follow.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Constructs 11–20", gap: 18,
    body: table(["#", "Construct at the first refusal", "Statements", "Functions"], more, [5, 69, 14, 12], { compact: true }) + bullets([
      "An index signature constrains every key of its kind. Row 11 has the negative case named-implicit-index; its record gives no source position. Row 13’s arms hold a count and a function; blocker-gap-round-captured-arms-reduction is its gap case. Canonicalization serializes contracts for comparison, omitting source positions. Row 17 has the negative case index-signature. Rows 18 and 20 are explained on “Decoders and checked storage”. These twenty rows cover 9,202 statements in 117 functions.",
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
    label: "Constructs 2–5 · cited source sites; measured weights on the ranking", title: "Later obligations occupy the leading sites", gap: 20,
    body: table(["Construct and site", "Recorded refusal", "What the source establishes"], [
      ["2. lowerFile: lowered.filter", "Closure expression claim at the lowered array before filter", "The array holds translated declarations. A filter callback checks references to omitted functions; the enclosing loop reassigns the array"],
      ["3. expr: callable initialization", "Source expression obligation at the returned withValue record", "The record carries a function, its initial fields and both types; the earlier destructured target check is passed"],
      ["4. readTypeTerm: quantified call", "Source expression obligation at a call reading a generic function type", "The call supplies type parameters, parameters and result type; the failed argument or result contract is unestablished"],
      ["5. hoisting: [...placed.keys()]", "Source expression obligation at an iterator spread", "placed is a Map from function declarations to their placement. Its keys are copied into an array in insertion order"],
    ], [28, 28, 44]) + bullets([
      point("Names", "lowerFile translates a file, expr reads an expression, readTypeTerm reads a type annotation, and hoisting arranges declarations bound before their statements. These are function names in tools/."),
      point("Evidence limit", "the sites confirm four distinct source forms. Their generic messages need isolated obligations before a common cause or remedy is asserted. The earlier cases are positive; their census functions face these further refusals."),
    ]),
  }),
  slide("round", {
    label: "Cited case expectations · pipeline/cases.mts; measured census comparison · WORK.md", title: "Cases and the functions they target", gap: 18,
    body: table(["Positive case (blocker-gap-round- prefix)", "What it checks", "First refusal in its census functions"], [
      [`early-capture ${status("ok", "positive")}`, "An outer arrow states its returned function type", "collectDeclarations: missing text in an interface base expression"],
      [`parent-walk ${status("ok", "positive")}`, "Recursive callbacks retain their declared parameters", "lowerFile and callers: lowered array read before filter"],
      [`assign-target ${status("ok", "positive")}`, "A destructured target is checked for undefined", "expr and callers: returned callable-initialization record"],
      [`scope-spread ${status("ok", "positive")}`, "A type-reading context record states the function fields it copies", "readTypeTerm and callers: quantified call for a generic function type"],
      [`indexed-for-of ${status("ok", "positive")}`, "Iteration over an indexed value or an empty array", "functionPlacement verifies; hoisting and callers reach a Map keys spread"],
    ], [29, 31, 40], { compact: true }) + bullets([
      point("Measured comparison", "897feac29b75 → aa376e0a92d8: 373/635 → 382/637 functions; 3,584/15,184 → 3,754/15,201 verified statements. Nine functions gained, none lost. files: realOf, findPackage. fragment-expressions: knownLocal, localArrow, memberOf, localValues, letWrites. fragment-statements: functionPlacement. written-applications: isInitializer. Each file name is in tools/ with suffix .mts."),
      point("Scope", "the five rows cite positive expectations. A case’s success does not establish its whole census function. The censuses count functions in their respective sources; the later source has two more functions."),
    ]),
  }),
  slide("storage", {
    label: "Constructs 18 and 20 · measured 109 and 101 statements", title: "Decoders and checked storage", gap: 22,
    body: code([
      "// readDiagnostic assembles decoded fields through this dictionary:",
      "const result: { [key: string]: unknown } = { ...d };",
      "// Later it assigns decoded parts, then asserts the diagnostic type.",
      "return result as unknown as ObligationDiagnostic;",
      "// decodeFlowDocument checks value, then aliases its storage:",
      "const document: unknown = value;",
      "return document as FlowDocument;",
    ]) + bullets([
      point("The names", "a decoder checks input and returns a typed value. d and value are parsed JSON records. ObligationDiagnostic describes a failed proof obligation; FlowDocument describes a graph of execution steps. unknown gives no shape; as asserts a type."),
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
      ["8. The refusal stays", "No route establishes the obligation at acceptable cost"],
    ], [25, 75], { compact: true }) + bullets([
      point("Effect", "a contract may bound how a call changes stored values. A host boundary’s result and effect are assumptions about its code."),
      "Before choosing a route, check for discarded type information and for assertions over storage whose writes the checks do not constrain. Construct 11’s record-to-index refusal protects keys its named fields do not describe; construct 17’s lookup may find inherited methods.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and scope", title: "First refusals in one fixed record", gap: 24,
    body: bullets([
      point("Measured", "census-tools-aa376e0a92d8-2026-10-31T14-31-26-964Z.json in the supplied census directory 2db902ca8b7b: clean commit aa376e0a92d8, tools/, 300-second stage limit. Counts come from function outcomes and the statement inventory."),
      point("Inspected", "The session’s work/refusals.json lists the refusals; tools/tools/slice-*.mts is in the cited census directory. All 255 details match the record. Source spans count UTF-16 code units, as TypeScript does. work/round/ranking.md lists every site, its weight, the top twenty case matches and repair assessments."),
      point("Source policy", "pipeline/cases.mts owns case expectations. WORK.md owns the census comparison. SOURCE-REWRITES.md owns the routes and decoder storage repair. No new pipeline run supplies a number in this deck."),
      point("Revision marks", "the marked page compares with deck commit f893d8b4, the base named in the intervening deck records. This is separate from the ordinary census comparison on “Cases and the functions they target”."),
      point("Limits", "Observed source forms are confirmed. Generic search failures leave the exact failed obligation to isolate. Later refusals and future gains are unmeasured. Construct 11 names one restriction but has no located obligation in this record."),
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
