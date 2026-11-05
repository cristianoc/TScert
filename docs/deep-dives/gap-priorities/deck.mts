/* Measured tools census 9bf8c463b7c9, 2026-11-02, 300-second stages.
 * Build: make deck NAME=gap-priorities SINCE=f893d8b4.
 * Site audit: `node dev/census.mts refusals <record>` on that census's record. */
import { bullets, card, cards, cover, point, slide, stat, table, type Deck, type Slide } from "../../../dev/deck.mts";

const measured = "Measured 2026-11-02 · complete tools census of 9bf8c463b7c9";
const first: string[][] = [
  [
    "1",
    "Array every used to justify a type predicate",
    "13.114",
    "784",
    "29"
  ],
  [
    "2",
    "Rest destructuring in a hoist-target effect",
    "9.955",
    "681",
    "25"
  ],
  [
    "3",
    "Array-presence field read in claim printing",
    "3.987",
    "296",
    "10"
  ],
  [
    "4",
    "Compiler result record with conditional implementation",
    "3.310",
    "27",
    "5"
  ],
  [
    "5",
    "Nested receiver-call expression record",
    "2.416",
    "812",
    "10"
  ],
  [
    "6",
    "Native-field array captured by a map callback",
    "2.095",
    "418",
    "5"
  ],
  [
    "7",
    "URL href access · existing host boundary",
    "1.818",
    "2",
    "2"
  ],
  [
    "8",
    "Activated-module map returned at its contract",
    "1.806",
    "24",
    "3"
  ],
  [
    "9",
    "Readonly call-effect metadata spread",
    "1.484",
    "7",
    "2"
  ],
  [
    "10",
    "Enum reverse-property descriptor lookup",
    "1.294",
    "17",
    "2"
  ]
];
const more: string[][] = [
  [
    "11",
    "Observed-resolution notes serialized as JSON",
    "1.156",
    "23",
    "2"
  ],
  [
    "12",
    "Renamed parameter record with a translated bound",
    "1.067",
    "762",
    "4"
  ],
  [
    "13",
    "Binder-reading scope object with a lookup callback",
    "1.009",
    "210",
    "3"
  ],
  [
    "14",
    "Compiler-client prototype · existing host boundary",
    "0.833",
    "2",
    "1"
  ],
  [
    "15",
    "Field read on a non-object: site unlocated",
    "0.769",
    "3",
    "1"
  ],
  [
    "16",
    "Effect-signature map result contract",
    "0.714",
    "4",
    "1"
  ],
  [
    "17",
    "Project cell read after a potentially writing step",
    "0.714",
    "4",
    "1"
  ],
  [
    "18",
    "Ancestor variable reassigned from its parent field",
    "0.714",
    "4",
    "1"
  ],
  [
    "19",
    "Loaded-module exports copy · existing host boundary",
    "0.714",
    "4",
    "1"
  ],
  [
    "20",
    "Spread-call obligation · source span unlocated",
    "0.667",
    "5",
    "1"
  ]
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end", title: "Where proofs of TScert’s own code fail",
    text: "TScert checks type claims about TypeScript programs. Its complete tools/ census verifies 489 of 679 functions: 72.0%. This deck explains what that counts, how the first refusal of each remaining function sets priorities, and what the measured round establishes. A failed proof search does not by itself show an unsafe program.",
  }),
  slide("terms", {
    label: "How to read the evidence", title: "A verified function and a small case answer different questions", gap: 26,
    body: cards([
      card("A verified function", "The parser reads source and annotations. A producer proposes type claims; proof search tries to justify them; an independent checker validates the evidence. A function verifies when its complete slice succeeds. A slice includes the function’s dependencies, which can contain its first refusal."),
      card("The safety boundary", "The checker’s type-safety result is proved in Lean, a proof assistant. Its application to TypeScript also relies on faithful source translation and audited external contracts. A contract states the results and effects assumed of code outside the checked source."),
      card("A pipeline case", "A small source has an expected outcome in pipeline/cases.mts. A positive case verifies. A negative case is refused and demonstrates unsafe behavior. A gap case records a missing capability. Success of one small source establishes that obligation; a larger caller can meet a further refusal."),
    ]),
  }),
  slide("find", {
    label: measured, title: "489 of 679 functions verify: 72.0%", gap: 24,
    body: cards([
      stat("34.9%", "Separate statement coverage: 5,487 of 15,715 counted executable statements.", "ok"),
      stat("190", "functions do not verify: 160 search refusals, 29 source restrictions, one timeout."),
      stat("300 s", "limit per process stage. classStmt in fragment-classes reaches the limit."),
    ]) + bullets([
      point("Function scope", "named top-level function declarations with bodies in tools/. Each counts once, including functions sharing a recursive slice. Unsupported, failed and timed-out functions stay in the denominator. Module initialization, class members and module-bound arrows are outside it."),
      point("Statement scope", "executable statements inside those functions, including their nested bodies. Every statement has equal weight. A verified function contributes all its counted statements; the 190 other functions own 10,228 statements."),
      point("A dependency’s refusal", "an initializer outside the headline function scope can nevertheless prevent a function slice from verifying. Neither percentage measures all project code."),
    ]),
  }),
  slide("method", {
    label: "Cited rule · dev/census.mts; inspected saved source sites", title: "Rank the first observed construct, not a generic error message", gap: 24,
    body: bullets([
      point("One function, one first refusal", "read its saved slice at the recorded source span. All saved slice hashes match the census. Shared recursive text still represents each named function separately. Later refusals are outside this ranking."),
      point("One construct per group", "split generic search failures using their source expressions and input contracts. The tables name observed constructs, not proved causal defects. A missing source location stays an unlocated obligation; it is not assigned an invented cause."),
      point("The priority weight", "a function with n statements contributes 10 / (10 + n). A 10-statement function contributes 0.5; a 90-statement one, 0.1. Add contributions for a group and sort by the full value. Tables round to three decimals. Smaller functions often have fewer later refusals."),
      point("An existing host boundary", "a small wrapper performs an external operation outside the model. Callers use its audited contract; its implementation remains refused. Rows 7, 14 and 19 are documented examples, whose implementation refusals alone call for no new language support."),
      point("Choosing work", "weights rank observed refusals. Choose further cases after checking which routes already answer or restrict them. Counts describe blocked code, not promised gains; all 190 functions and their 10,228 statements contribute once."),
    ]),
  }),
  slide("priority", {
    label: measured, title: "The ten leading first-refusal groups", gap: 18,
    body: table(["#", "Observed construct or obligation", "Weight", "Statements", "Functions"], first, [4, 60, 12, 13, 11], { compact: true }) + bullets([
      "A type predicate (1) claims a test narrows its input. An effect (2, 9) bounds changes a call can make. Array presence (3) records whether indexed elements exist. A receiver call (5) passes an object as this. Row 7 is the URL-string host boundary; its internal href read is refused. Row 10 reads a property descriptor, which describes a property rather than invoking it.",
    ]),
  }),
  slide("priority-more", {
    label: measured, title: "Groups 11–20: smaller functions also matter", gap: 18,
    body: table(["#", "Observed construct or obligation", "Weight", "Statements", "Functions"], more, [4, 60, 12, 13, 11], { compact: true }) + bullets([
      "A bound (12) limits a type parameter. A binder (13) names one; its scope supplies lookup operations. A cell (17) holds a mutable local whose contract must survive intervening effects. Rows 15, 17 and 20 lack a located source span: their messages establish obligations, not specific causes. Rows 14 and 19 are the compiler-prototype and loaded-exports host boundaries. These twenty groups cover 109 functions and 4,089 statements.",
    ]),
  }),
  slide("leading-sites", {
    label: "Inspected source sites · full paths and spans in census.mts refusals of that census", title: "The leading sites expose further obligations", gap: 20,
    body: table(["Source under tools/", "Observed first refusal", "Scope of the evidence"], [
      ["1. type-term · expandIdentity", "An every test is offered as a predicate excluding null array elements", "The promised narrowing is not established at this return"],
      ["2. fragment-statements · hoistTarget", "Destructuring declares the first item and a rest array", "The function’s stated preservation effect is not established"],
      ["3–4. claim-text · atomText; compiler-channel · current", "Read array presence; build a conditional compiler-result record", "Expression typing claims fail; a shared low-level cause is unestablished"],
      ["5–6. fragment-expressions · wrappedMethodCall; declaration-graph · elaborateDeclaration", "Build a nested receiver-call record; capture native fields in a map", "Separate expression and closure claims fail in dependent slices"],
    ], [30, 40, 30], { compact: true }) + bullets([
      "Names identify the source operations, not only the top-level slices that retain them. Rows 7, 14 and 19 retain the audited URL-string, compiler-prototype and module-exports boundaries. Their callers use the documented contracts. A case for an earlier refusal is not an exact reproducer of a later obligation. The current ranking records the source expression and failed judgment separately; it makes no claim that one shared implementation defect explains a whole group.",
    ]),
  }),
  slide("round", {
    label: "Measured main comparison · ca4e3c8a → 9bf8c463b7c9 · tools/", title: "460 / 680 → 489 / 679 verified functions", gap: 24,
    body: cards([
      stat("67.6% → 72.0%", "Front-end function coverage. Twenty-nine functions gain verification; none loses it.", "ok"),
      stat("32.8% → 34.9%", "Statement coverage: 5,183 / 15,817 → 5,487 / 15,715.", "ok"),
      stat("0 → 1", "Stage timeouts. classStmt was already unverified; its timeout is a performance regression.", "neg"),
    ]) + bullets([
      point("Denominators move", "declarationAnswer, an unverified forwarding helper, is deleted. Matched statement inventory retains all 5,183 previously verified statements and gains 301; within the census scope, 106 statements are deleted and four added. Net verified statements increase by 304, including three added statements."),
      point("Where functions gain", "compiler branding, package-installation checks, recording, compiler opening, definition assembly, global signature lookup and alias classification contribute gains. These are full-census function outcomes, separate from small-case success."),
      point("Comparison scope", "both records cover the complete tools/ function census at 300 seconds. This is the round’s main-to-main comparison; revision highlighting uses a different baseline, the last owner-approved deck."),
    ]),
  }),
  slide("performance", {
    label: "Measured producing-execution costs · ca4e3c8a → 9bf8c463b7c9", title: "Search cost rises in refused type-term slices", gap: 24,
    body: table(["Search measure and scope", "Before", "After"], [
      ["CPU seconds · all unique producing executions", "2,909.2", "6,088.0"],
      ["CPU seconds · 460 functions verified in both records", "1,446.5", "1,345.7"],
      ["CPU seconds · 20 distinct refused type-term slices, 29 functions", "50.9", "3,354.7"],
      ["Maximum recorded search peak · all functions", "2,508 MiB", "2,140 MiB"],
    ], [58, 21, 21]) + bullets([
      point("How costs count", "CPU is user plus system time. Each scope counts a producing execution once, even when many functions refer to it. Replays retain historical producing costs; these are not CPU consumed by replay lookups. Maximum memory is one recorded process peak."),
      point("Rows are not additive", "the global row includes the subsets. Function cohorts can share executions: five final executions overlap cohorts, totaling 10.669515 seconds. The global total removes that overlap; each cohort deduplicates within its own scope."),
      point("What the comparison establishes", "the retained verified cohort costs less; the refused type-term slices cost more and report a later first refusal. Inputs, contracts and verifier implementations differ. These observations establish neither a same-work project speed ratio nor the cause of the new classStmt timeout."),
    ]),
  }),
  slide("storage", {
    label: "Cited source contracts and executable cases", title: "Retain known contracts, then check their definitions", gap: 24,
    body: cards([
      card("Compiler identity is JSON data", "blocker-round-compiler-identity-json verifies with the constructor’s full field union and its JSON-data bound. The actual current function reaches the later result-record obligation in group 4. JSON-safe data must account for every field; an assertion of a convenient shape cannot establish it."),
      card("Owned matcher preservation", "blocker-round-global-signature-matcher verifies. Its string-comparing matcher preserves existing array storage on normal return, including lengths and which indices are present. globalEntry verifies in this census. A matcher using pop shortens the array and violates that guarantee; the falsely promised version is refused and throws TypeError under Node."),
      card("A semantic binder printer", "blocker-round-binder-entries verifies using the shared complete type-term printer before serialization. The larger mergeRefusal function reaches the scope-object obligation in group 13. The source repair compares semantic fields, retaining declaration-identity spans."),
    ]) + bullets([
      point("Use the whole contract", "a footprint describes allowed value and store changes. A qualified callback must establish it from its body. A normal-return guarantee supplies no preservation when the call throws. The existing effect checks and negative cases guard that boundary."),
    ]),
  }),
  slide("routes", {
    label: "Cited policy · docs/SOURCE-REWRITES.md", title: "Choose the first route that establishes the obligation at acceptable cost", gap: 20,
    body: table(["Route", "Required evidence"], [
      ["Support", "A checked rule or audited external contract admits the construct"],
      ["Runtime check", "An executable check establishes the complete required property"],
      ["Repair", "The source corrects a defect exposed by the refusal"],
      ["Avoidance", "An equivalent source form preserves returns, exceptions and effects"],
      ["Host boundary", "A small wrapper performs an external service operation; callers assume its audited contract"],
      ["Trusted unit", "The owner accepts a local unit’s complete contract as an assumption"],
      ["Proof", "A Lean proof establishes the required fact in the model"],
    ], [25, 75], { compact: true }) + bullets([
      "First inspect whether the source discards information its own construction already establishes. A negative case needs demonstrated unsafe behavior. A refused ordinary program remains an obligation to investigate, even when another source form verifies. The status table in WORK.md owns each investigation’s status.",
    ]),
  }),
  slide("sources", {
    label: "Evidence and revision scope", title: "A fixed census, source sites, and a comparable baseline", gap: 24,
    body: bullets([
      point("Final record", "census-tools-9bf8c463b7c9-2026-11-02T20-28-59-581Z.json, saved in census directory 2db902ca8b7b. It records clean main 9bf8c463b7c9, complete tools/, the 300-second process-stage limit, function outcomes and statement inventory."),
      point("Source inspection", "the record’s tools/tools/slice-*.mts files match their recorded SHA-256 hashes. Source offsets count UTF-16 code units. Session deck-final/sites.json, site-contexts.md and ranking.md retain the exact locations, texts, group membership and arithmetic."),
      point("Comparison and ownership", "merged-main-census.json records ca4e3c8a; main-final-comparison.txt compares it with the final record; census-cost-investigation.md audits producing-cost scopes and overlap. DESIGN.md defines metrics; WORK.md owns dated movement; cases.mts owns expectations. SOURCE-REWRITES.md owns the existing boundaries: URLs as strings, The compiler client’s prototype, and A loaded module’s own exports."),
      point("Revision marks", "the marked page compares with f893d8b4, the last owner-approved deck. This is a visual revision baseline, not the round’s measurement baseline. Changed text and slides are marked in a separate page and Slides-format project; the checked-in project is unmarked."),
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert’s proofs fail", slides,
  sections: [
    { description: "The measured scope and first-refusal ranking.", start: "cover" },
    { description: "Leading groups and their observed source obligations.", start: "priority" },
    { description: "Coverage, performance, checked contracts and evidence.", start: "round" },
  ],
};
export default deck;
