/* Supplied census b644972daee6, 2026-11-01.
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Audit: session scratchpad, work/round/ranking.md. */
import { bullets, card, cards, cover, point, slide, stat, table, type Deck, type Slide } from "../../../dev/deck.mts";

const measured = "Measured 2026-11-01 · census of b644972daee6";
// Weight: sum of 10 / (10 + each function's census statement count).
const first: string[][] = [
  ["1", "Mapped-type field key converted to text", "13.114", "784", "29"],
  ["2", "Switch-clause reduction builds nested statement blocks", "9.955", "681", "25"],
  ["3", "Element-kind serialization fails its preservation contract", "7.645", "78", "10"],
  ["4", "Installation file paths mapped into a Set", "6.008", "54", "9"],
  ["5", "Mapped directory-entry pairs serialized as JSON", "4.611", "111", "9"],
  ["6", "Build-part union read before choosing spread or expression", "4.290", "72", "7"],
  ["7", "Named record used at an index signature", "4.277", "248", "8"],
  ["8", "Numeric claim field converted to text", "3.987", "296", "10"],
  ["9", "Launcher and directory paths flattened through a helper", "3.358", "26", "5"],
  ["10", "Mapped installation array captured by a nested loop", "2.981", "39", "5"],
];
const more: string[][] = [
  ["11", "Checked compiler client asserted as its private interface", "2.589", "26", "4"],
  ["12", "Reassigned translated-function array read before map", "2.542", "798", "6"],
  ["13", "Observation result assembled from captured recording fields", "2.439", "73", "5"],
  ["14", "Receiver argument translated after translating the callee", "2.417", "794", "10"],
  ["15", "Project-check callback before reading the project", "2.079", "50", "4"],
  ["16", "Call-effect record spread with exceptional preservation", "1.828", "26", "3"],
  ["17", "Parameter-string map captures a required-parameter count", "1.746", "175", "5"],
  ["18", "Compiler child lookup through Reflect.get", "1.667", "4", "2"],
  ["19", "Compiler snapshot update with a conditional changed-file record", "1.648", "26", "3"],
  ["20", "Generic binder mapped with a stronger bound", "1.603", "5", "2"],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end", title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. This deck explains its first refusals when it checks the functions of its own source-reading code, in tools/. The supplied census of b644972daee6 measures 380 of 637 functions verified. The next two slides explain the measurement. Source constructs at the remaining functions’ first refusals determine the priority order.",
  }),
  slide("terms", {
    label: "How to read the result", title: "A checked function, a refusal, and a small case", gap: 26,
    body: cards([
      card("Verified and refused", "The parser reads source and annotations. The producer proposes type claims. A proof search tries to justify them, and a checker validates the evidence. A function is verified when this whole path succeeds. A refusal names an unsupported source form or an obligation the proposed evidence cannot establish."),
      card("The safety boundary", "The checker’s type-safety result is proved in Lean, a proof assistant. Applying it to source also relies on faithful parsing and contracts: descriptions of external code taken as assumptions. A failed search alone establishes neither a source bug nor an unsafe program."),
      card("A case", "A small TypeScript file has an expected outcome in pipeline/cases.mts. A positive case must verify. A negative case must be refused and show unsafe behavior. A gap case records a missing capability. An exact case shows the refused construct; a related case shows only part of it."),
    ]),
  }),
  slide("find", {
    label: measured, title: "380 of 637 functions verify", gap: 26,
    body: cards([
      stat("26.0%", "3,965 of 15,224 census statements belong to verified functions.", "ok"),
      stat("257", "functions are refused: 230 at search, 27 at source or proposal restrictions."),
      stat("0", "stage timeouts, with a limit of 300 seconds per process stage."),
    ]) + bullets([
      point("A slice", "a copy of one top-level function and its dependencies, run through the pipeline. A refusal can occur in a dependency retained in the copy."),
      point("Blocked statements", "each refused function’s statements count once, at its first refusal: 11,259 statements. Statements include returns, assignments and tests. Later refusals are outside this measurement."),
      point("The source", "the supplied census-tools-b644972daee6 record and refusals.json. Every number describes those stored results; no new pipeline run supplies a measurement in this deck."),
    ]),
  }),
  slide("method", {
    label: "Cited priority rule · dev/census.mts, refusals; measured sites in the supplied slices",
    title: "Priority favors reasons blocking many small functions", gap: 26,
    body: bullets([
      point("Each function contributes", "10 / (10 + its statement count). A function with 10 statements contributes 0.5; one with 90 contributes 0.1. Smaller functions tend to have fewer further refusals behind their first."),
      point("A group’s weight", "the sum of those contributions. Groups appear in descending weight, rounded to three decimals in the tables. The statement and function columns give the code each group blocks. Weight is a priority rule; future gains are unmeasured."),
      point("One construct per group", "a generic failed-search message is split by its refused expression and the functions reaching it. Field-key conversion and numeric-claim conversion are separate groups, with different input contracts. Shared syntax identifies an observed construct; it does not prove a common defect."),
      point("Read the sites", "all 257 refusal details agree with the record, and every refused slice matches its recorded source hash. The leading twenty groups’ source contexts and case comparisons are in work/round/ranking.md and site-contexts.md in session storage."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten leading observed constructs", gap: 18,
    body: table(["#", "Construct at the first refusal", "Weight", "Statements", "Functions"], first, [4, 60, 12, 13, 11], { compact: true }) + bullets([
      "A mapped type computes fields from keys. Row 3 serializes allowed element kinds while promising to preserve stored values and array contents. A build part (6) describes either a spread or a single expression in object construction. An index signature (7) constrains every key of its kind. Rows 4 and 10 concern installed packages’ declaration files; row 9 expands paths into their named forms. The detail slide locates these constructs.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Constructs 11–20", gap: 18,
    body: table(["#", "Construct at the first refusal", "Weight", "Statements", "Functions"], more, [4, 60, 12, 13, 11], { compact: true }) + bullets([
      "A compiler client (11) communicates with TypeScript. Observations (13) record file-system answers. A call effect bounds changes on normal return; row 16 adds that bound when a call throws. Reflect.get (18) reads a property by key; the source-admission check lacks its contract. A snapshot (19) is a compiler view of files. A binder (20) is a type parameter, with a bound limiting its types. These twenty groups cover 4,366 statements in 161 functions.",
    ]),
  }),
  slide("leading-sites", {
    label: "Cited slice sites · measured weights on the ranking", title: "Leading constructs occur inside shared helpers", gap: 20,
    body: table(["Rank and source function", "What its refused source does", "Evidence and case scope"], [
      ["1. type-term: expandIdentity", "Converts a field key to text for an error about a missing mapped-type field", "Expression typing search fails; key-stringify and unknown-string are related positive cases"],
      ["2. fragment-statements: switchStmt", "Reduces switch clauses into nested blocks, appending each clause’s translated statements", "Search cannot derive the callback’s return contract; no exact small case identified"],
      ["3. named-record: kindsText", "Maps allowed element kinds through JSON serialization, then joins their text", "The claimed preservation effect is not established; no exact small case identified"],
      ["4–6. checkedInstallation, direntsRead, mapExprParts", "Construct a path Set; serialize directory-entry pairs; choose a build part’s branch", "Distinct expression typing failures; mapped-json is a gap case for row 5’s construct"],
      ["7–10. record conversion, atomText, profile, installations", "Require an index contract; print a numeric claim; flatten paths; capture a mapped array", "Row 7 has named-implicit-index, a negative case; the other comparisons are related or absent"],
    ], [27, 38, 35], { compact: true }) + bullets([
      "Module names identify files under tools/; function names identify the operations described beside them. Case names abbreviate blocker-gap-round-key-stringify and blocker-round-unknown-string or blocker-round-mapped-json. A dependency can carry one helper’s refusal into many slices. The index-signature refusal gives no source span; inspected candidate conversions have no assigned refusal location.",
    ]),
  }),
  slide("round", {
    label: "Measured ordinary census comparison · supplied records of 13d2104e09a9 and b644972daee6",
    title: "369 → 380 verified functions; one function loses verification", gap: 24,
    body: cards([
      stat("+12", "functions gain verification relative to the census described by the preceding deck.", "ok"),
      stat("−1", "kindsText in named-record loses verification at its claimed preservation effect.", "neg"),
      stat("+563", "verified statements: 3,402 / 15,206 → 3,965 / 15,224.", "ok"),
    ]) + bullets([
      point("Gains in diagnostic", "diagnosticNode, diagnosticOutcome, directJudgment, readDiagnostic, sourceMap and span: six helpers for decoding and presenting proof failures."),
      point("Other gains", "promiseText in named-record prints the fact a guard or assertion function establishes about an argument; sameEffect and samePromise in type-term compare call contracts; decodeCallEffect and decodeGraph in type-graph decode them; nodeAt in type-probe finds a compiler node."),
      point("Comparison scope", "this uses the preceding deck’s census. WORK.md owns the round’s separate comparison of main commits 8ec44f16ba8d and b644972daee6: 382 → 380 verified functions, seven gains and nine losses. A small case’s expected success establishes only that source’s obligation."),
    ]),
  }),
  slide("storage", {
    label: "Cited sources · tools/claim-text.mts, compiler-channel.mts, diagnostic.mts, source-flow.mts",
    title: "Preserve the information the source already has", gap: 24,
    body: cards([
      card("Field-key collection · rank 1", "The mapped-type helper collects only strings, but declares its local array with a broader property-key type that also admits objects representing symbol keys. That discards the string-only fact before conversion to text. A string-array contract preserves what the collector establishes; its full census outcome is unmeasured."),
      card("Private compiler client · rank 11", "The decoder checks that methods are functions, then asserts the private interface over existing storage. Callable presence alone does not establish their argument and result contracts. This site needs a contract audit; the record supplies no proof of its precise failed obligation."),
      card("Typed decoder results", "A decoder checks input and returns a typed value. readDiagnostic constructs typed results and verifies in this census. decodeFlowDocument builds fresh records from checked fields; its first refusal is an expression typing obligation at a fresh record describing an execution step."),
    ]) + bullets([
      point("Repair assessment", "rank 1 loses its string-only collection contract. Rank 8 tests a numeric conversion result, which does not establish that the original claim field is primitive; explicit primitive tests are a repair candidate. Rank 11 needs its whole callable contract justified. Each outcome needs validation."),
    ]),
  }),
  slide("routes", {
    label: "Cited policy · SOURCE-REWRITES.md", title: "Use the first route that establishes the obligation at acceptable cost", gap: 20,
    body: table(["Route", "What the route requires"], [
      ["1. Support", "A rule or external contract admits the construct"],
      ["2. A runtime check", "An executable check establishes the whole property"],
      ["3. A repair", "The source corrects a defect the refusal reveals"],
      ["4. Avoidance", "An equivalent source form avoids costly support"],
      ["5. A host boundary", "A small wrapper performs an external service operation with no model. Its functions stay refused; callers assume its audited result and effect contract"],
      ["6. A trusted unit", "Local code is exempt from checking, with the owner accepting its full contract as an assumption"],
      ["7. A proof", "A Lean proof establishes the needed fact in the model"],
    ], [25, 75], { compact: true }) + bullets([
      "Before choosing a route, inspect whether the code discards information it already has. An external declaration is a specification to audit. A successful small case can establish a route for its construct while the larger census function reaches another refusal. Later obligations are outside this record’s first-refusal ranking.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and scope", title: "One fixed record, inspected at its refusal sites", gap: 24,
    body: bullets([
      point("Measured", "census-tools-b644972daee6-2026-11-01T04-58-18-481Z.json in the supplied census directory 2db902ca8b7b: clean commit b644972daee6, tools/, 300-second process-stage limit. Function outcomes and the statement inventory supply the counts."),
      point("Inspected", "the supplied work/refusals.json and tools/tools/slice-*.mts in that census directory. All 257 details match the record, every refused slice matches its recorded hash, and each recorded span selects the group’s expression. Positions count UTF-16 code units, as TypeScript does."),
      point("The ranking", "work/round/ranking.md in session storage gives every group’s weight, statements, functions and sites, with case comparisons and repair assessments for the first twenty. site-contexts.md retains those groups’ source contexts. Generic failures locate constructs whose exact failed proofs need isolation."),
      point("Source policy", "pipeline/cases.mts owns case expectations. WORK.md owns round coverage movement. SOURCE-REWRITES.md owns the seven routes and typed decoder repairs. This deck’s comparison with its preceding census is labelled separately."),
      point("Revision marks", "the marked page compares with deck commit f893d8b4, the base named in the intervening deck records. Changed text is marked in the standalone page and a separate Slides-format project in session storage."),
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert’s proofs fail", slides,
  sections: [
    { description: "The census and how first refusals become a ranking.", start: "cover" },
    { description: "The leading observed constructs and their evidence.", start: "priority" },
    { description: "Coverage movement, source checks and routes for a refusal.", start: "round" },
  ],
};
export default deck;
