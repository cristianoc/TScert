/* The knowledge-growth deep dive: why the census of d578dd8 searches several
 * times longer than that of 5dfb065, and the pass that gave heap knowledge one
 * stored form. Heap facts about one field were added and never merged, so a
 * condition testing a field n times stored values growing as about n³; a rule
 * merged in d578dd8 made TScert's own code reach it. The pass stores each fact
 * once per alias class, measured each function against main, and found and
 * removed a second regression on the way. Built with the deck kit
 * (`make deck NAME=knowledge-growth`). */
import { bullets, card, cards, code, color, columns, cover, inline, panel, para, point, slide, stat, status, table, type Deck, type Slide } from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** Prose with `code` in backticks, as the kit's `inline` reads it. */
const t = inline;
/** A name from the sources, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
const measured = status("neutral", "measured"), defect = status("neg", "defect"), added = status("ok", "added");

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · a cost regression",
    title: "One condition, 300 MB of evidence",
    text: t("TScert regularly checks every function of its own front end, the code in `tools/`; that run is the census. On 2026-10-27 five branches were merged after commit 5dfb065, and the census after them verifies 15 more functions, but its proof search takes 3.4 times the CPU, and one run of the checker peaks at 10.6 GB. The cause is how TScert stores what it knows about object fields: a new fact about a field is added beside the old ones, never merged with them, so a condition testing one field n times stores a number of values growing as about n³. That storage is in the repository’s first commit; a rule merged that day made TScert’s own code reach it. This deck shows where, how it multiplies, which mistakes let it through, what the pass of work that followed changed, the second regression that pass found in itself, and what prevents a regression of this kind."),
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert proves a function, in four cards", gap: 24,
    body: cards([
      card("Search, evidence, checker", "TScert verifies a TypeScript function by proving it safe. An untrusted search builds the proof, a JSON document called the evidence; a checker written and proved in Lean, a proof assistant, reads it and accepts or refuses. Both handle the same evidence, so its size drives the time and memory of both."),
      card("Slot", t("The checked program is a graph of steps, each storing its result in a numbered slot. Every read makes a new slot: reading `node` twice gives two slots holding the same object.")),
      card("Heap fact", t("What is known at one point of the function about a field of an object: “the object in slot 4 has a field `kind` holding one of these values”. A fact is a slot, a field and a list of values. A test such as `node.kind === 0` adds one on its edges.")),
      card("Knowledge", "The heap facts that hold at one point of the function. The evidence stores each distinct knowledge once, in a table, and each point refers to its entry by number."),
    ], 2),
  }),
  slide("measured", {
    label: "What the census showed", note: `each stage of a run limited to 300 s · ${measured}`,
    title: "15 more functions verify, at 3.4 times the search CPU", gap: 22,
    body: table(["", "census of 5dfb065 (before)", "census of d578dd8 (after the merges)"], [
      ["functions of tools/ verified (the merged code added 6)", "212 of 513", "227 of 519"],
      ["search: CPU over the census, peak memory of one run", "254.7 s, 1.5 GB", "858.6 s, 8.8 GB"],
      ["checker: CPU over the census, peak memory of one run", "62.5 s, 0.6 GB", "248.0 s, 10.6 GB"],
      [t("one function, `moduleFunction`: its search"), "6.7 s", "47.8 s"],
      [t("one function, `confined`: its search"), "27.1 s", "177.0 s"],
    ], [40, 30, 30]) +
      para(t("The census runs each function alone, with what it calls. `moduleFunction`, run on the two branches that differ in the rule (“What the branch changed”):"), 26) +
      table([t("`moduleFunction`"), t("without the rule (`gap-in-unknown`)"), t("with the rule (`gap-nullable-field`)")], [
        ["evidence written", "4.9 MB", "300.7 MB"],
        ["values stored in its heap facts", "2,149", "7,031,005"],
        [t("heap facts at the busiest point of a function it calls, `resolve` (next slide)"), "0", "132"],
      ], [40, 30, 30]),
  }),
  slide("where", {
    label: "Where the facts pile up", note: t("`tools/fragment-expressions.mts`, the function `visit` inside `resolve` · ") + measured,
    title: "Eleven guards in one condition", gap: 22,
    body: columns([
      code(["const visit = (n: Node): void => {", "  …", "  if ((ts.isParameterDeclaration(n) ||", "       ts.isVariableDeclaration(n) ||", "       ts.isBindingElement(n) ||",
        "       ts.isFunctionDeclaration(n) ||", "       … 6 more …", "       ts.isImportClause(n)) && name …) {", "    …", "  }", "  n.forEachChild(visit);", "};"]),
      para(t("Each `ts.isX(n)` is a call of TypeScript’s compiler API that tests `n.kind`, a field holding one of about 300 numbers, the members of the enum `ts.SyntaxKind`. Each guard that answers `false` adds a fact: `n.kind` is one of the numbers the earlier guards did not take."), 26) +
      para("Heap facts at successive points of the condition, with the rule, read from the evidence:", 26) +
      code(["2, 6, 12, 20, 30, 42, 56, 72, 90, 110, 132"]) +
      para(t("After k guards there are k × (k + 1) facts: both the facts on each slot holding `n` and the number of those slots grow with k (“What the points hold”, next). So the count grows with the square of the guards; each fact lists about 300 numbers."), 26),
    ], [48, 52]),
  }),
  slide("one-point", {
    label: "What the points hold", note: t("this function, without the rule (`gap-in-unknown`, `b6a0dc93`), read from its evidence · ") + measured,
    title: "Each failed test adds a fact to every copy of the object", gap: 22,
    body: columns([
      code(["type Kind = 0 | 1 | … | 99;", "type Node = { readonly kind: Kind };", "", "export function anyOf(node: Node): boolean {", "  if (node.kind === 0 || node.kind === 1 ||", "      node.kind === 2 || node.kind === 3)",
        "    return true;", "  return false;", "}"]) +
        table(["point", "facts on kind, on each slot holding node"], [["after the 1st failed test", "1, of 99 values"], ["after the 2nd", "2, of 99 and 98"], ["after the 3rd", "3, of 99, 98 and 97"]], [45, 55]),
      bullets([
        point("Old facts stay", "each failed test adds a smaller list beside the earlier ones. The list of 97 values implies those of 98 and 99, which stay stored."),
        point("Every copy of the object gets one", t("several slots hold the object `node` refers to (the evidence links them as aliases: 4 after the 1st test, 6 after the 3rd), and each fact is stored once per slot. The last test answers by returning, so its fact reaches no stored point.")),
        point("Answers are written out", t("“not 0” is the 99 other members of `Kind`, so a fact is as long as the type.")),
        point("What is needed", t("one fact per point: after the 3rd test, `node.kind` is in `Kind` except 0, 1, 2. Stored instead: 18 lists, 1,764 values.")),
      ], 25),
    ], [46, 54]),
  }),
  slide("multiply", {
    label: "How it multiplies", note: t("the function of the previous slide with n tests: without the rule (`gap-in-unknown`) → on main (`d578dd8`) · ") + measured,
    title: "Doubling the tests multiplies the stored values by about 8", gap: 22,
    body: table(["tests in the condition", "heap facts at the busiest point", "values stored in all heap facts", "evidence written"], [
      ["4", "18 → 24", "95,646 → 144,328", "7.3 MB → 9.3 MB"],
      ["8", "70 → 80", "762,992 → 945,398", "42.4 MB → 50.1 MB"],
      ["16", "270 → 288", "6,219,164 → 6,953,434", "300.0 MB → 331.0 MB"],
    ], [22, 26, 30, 22]) +
      para("Four factors multiply; the first three grow with the number of tests n:", 26) +
      bullets([
        point("Facts per slot", "one per failed test, about n."),
        point("Slots holding the object", "they grow with the tests: 6, 10 and 18 at 4, 8 and 16 tests (n + 2)."),
        point("Distinct points", "each test’s edges carry their own knowledge, about n."),
        point("Values per fact", t("the size of the field’s type: 100 for `Kind`, about 300 for `SyntaxKind`.")),
      ], 25) +
      para("So the stored values grow as about n³ times the type’s size, and the evidence 5 to 7 times per doubling. The growth is there without the rule.", 26),
  }),
  slide("branch", {
    label: "What the branch changed", note: t("`gap-nullable-field`, commit `a7b7843d`, merged in `05041cf0` · ") + added,
    title: "A rule that keeps the facts across a call", gap: 24,
    body: para(t("The rule `call-keep`: a call whose declared effect (the fields its declaration says it may write) writes no field of an object that existed before the call keeps every heap fact (soundness proved in Lean, `PromiseCalls.keepsHeap_prefix`). Before it, every call ended with no heap facts. The branch also adds `link-fact` (a field read into a slot holds one of the values the slot’s type allows), which gives the extra fact per slot in 18 → 24."), 26) +
      columns([
        panel("Before the rule", para(t("each `ts.isX(n)` in `visit` is a call, so it ended with no heap facts, and no guard’s answer survived to the next guard: 0 facts."), 24)),
        panel("With the rule", para(t("the compiler’s guards change nothing, so their calls keep the facts. The eleven guards now behave like a condition of eleven `===` tests: 132 facts."), 24)),
      ]) +
      para("The rule was reviewed as sound, and is. It did not create the growth: it removed the calls that had been hiding it.", 26),
  }),
  slide("mistakes", {
    label: "The mistakes", title: "Three mistakes let it through", gap: 24,
    body: cards([
      card(`1 · Storage with no normal form ${defect}`, t("`Facts := List Fact` (`HeapFacts.lean:199`): knowledge holds when every fact in the list holds. Nothing keeps one fact per field: a new fact is never merged with the facts on its field, a fact names a slot rather than the object, and an answer is the full list of values it leaves. All three are in the repository’s first commit, 2026-10-16.")),
      card(`2 · No test of how it scales ${defect}`, "TScert’s test cases are small: each tests a few conditions, so a cost that grows with the length of a condition passes them all. No test measures how the evidence grows when a construct is repeated."),
      card(`3 · Cost was not part of the merge ${defect}`, t("The branch measured only the functions it targeted (`setLiterals`: 433 KB of evidence in the census after the merge). The review asked about soundness, generality and tests. The integrating session, Claude, merged on passing tests. Only the census after the merge measured cost.")),
    ], 3),
  }),
  slide("pass", {
    label: "What the pass changed", note: t("commits `27798079` and `45bd0e40` · the theorems named are proved in Lean"),
    title: "Each fact stored once, about its alias class", gap: 22,
    body: cards([
      card("Alias class", t("The slots known to hold one value: linked as aliases, or reading one field of one object. A class is named by its least slot. Facts are stored once, on that slot, and every rule reads a slot through its class.")),
      card("Value set", t("A fact’s values are one set per kind of value; numbers and strings are written as these literals or as every literal but these. After three failed tests, `node.kind` is every number but 0, 1, 2: one fact, three literals.")),
      card("Normal form", t("At each point but a cut (a point whose knowledge the source states), the search stores one fact per class and field, combining everything it knows there. Proved: it holds exactly where the stored knowledge does, and it is its own normal form (`KnowledgeNormal.norm_holds`, `holds_of_norm`, `norm_idem`).")),
      card("Separation, and the evidence", t("Separation facts say two fields are different heap locations, so writing one keeps what is known of the other: a slot, some of its fields, and the slots and fields they differ from. They are stored grouped, proved to state exactly what they did and to be no more facts than before (`compact_holds`, `compact_size`). The evidence writes each distinct value set once, in a table.")),
    ], 2),
  }),
  slide("second", {
    label: "A second regression, found in the pass", note: t("a census of one function, `collect`, alone: before the pass (`b59096f`), after its first commit (`27798079`), after the fix (`45bd0e40`) · ") + measured,
    title: "The totals fell; one function got ten times slower", gap: 22,
    body: table([t("`collect`, `tools/fragment-statements.mts`"), t("before the pass"), t("after `27798079`"), t("after the fix")], [
      ["search CPU", "1.3 s", "14.3 s", "1.7 s"],
      ["checker CPU", "0.8 s", "3.4 s", "0.9 s"],
      ["evidence written", "4.5 MB", "7.6 MB", "3.1 MB"],
    ], [34, 22, 22, 22]) +
      bullets([
        point("How it was found", "the six costly functions of “Where it stands” were measured one by one against main, after their total had fallen; the total hid it."),
        point("What was observed", "separation stored as single pairs, one per field on each side, sorted at every point, and restated on every slot of both classes whenever a step or an edge read it. Removing that removed the rise."),
        point("Fix", t("separation stored grouped (`SeparationNormal.compact`, proved to state exactly what the separation states). The checks that read it, at an edge and at a write, compare by class instead of restating (`checkBy`, `apartBy`, proved sound).")),
      ], 25),
  }),
  slide("results", {
    label: "Where it stands", note: t("`b59096f` (before the pass) → after it, measured on 2026-10-28 · ") + measured,
    title: "Evidence up to 100 times smaller; some searches longer", gap: 22,
    body: table(["", "before the pass", "after it"], [
      [t("`node.kind === 0 || … || node.kind === 15`: evidence"), "319.3 MB", "3.2 MB"],
      [t("`node.kind === 0` repeated 16 times: evidence"), "93.2 MB", "1.9 MB"],
      [t("`node.kind === 0` repeated 32 times: search CPU, checker CPU"), "40.2 s, 18.8 s", "47.5 s, 9.0 s"],
      [t("`moduleFunction`: evidence"), "300.7 MB", "3.8 MB"],
      [t("six costly functions of `tools/`: search CPU, checker CPU, peak memory of one run"), "269 s, 54 s, 5.3 GB", "72 s, 11 s, 1.0 GB"],
      [t("two of them, `collect` and `closeStatements`: search CPU"), "1.55 s, 1.13 s", "1.89 s, 1.59 s"],
    ], [52, 24, 24]) +
      para(t("Every test case of TScert’s pipeline keeps its expected outcome: 2,357 of 2,357, 2,991 functions verified. Some searches take longer: 18% to 41% in the rows above. Profiles of `collect` put the added time in reading by class, mostly in computing each slot’s set of values from its type again at every point (sampled, not proved). The owner accepted this cost on 2026-10-28; computing that set once per type is open."), 25),
  }),
  slide("prevention", {
    label: "What prevents the kind", title: "A bounded form, then measurement per function", gap: 22,
    body: table(["In place", "What it bounds"], [
      ["The normal form, proved to keep exactly what holds", "where it is stored, by its definition: one value fact per class and one field fact per class and field, whatever the number of tests"],
      ["Value sets: what a test excludes is removed from one set", "a field’s tests at a point make one fact, not one per test"],
      [t("Grouped separation (`compact_size`, proved)"), "no more separation facts than it is built from, each slot it differs from once, each field once"],
    ], [44, 56]) +
      para(status("gap", "open") + t(": the scaling functions above (4 to 32 repetitions) as pipeline test cases, failing when the evidence grows faster than the repetitions; measuring each costly function against main before a change of the search or of Lean merges, as a written rule; a check that the evidence is in normal form; `node.kind` tested 32 times in one condition, which still exceeds the 60 s limit."), 25),
  }),
];

const deck: Deck = {
  title: "One condition, 300 MB of evidence",
  slides,
  sections: [
    { description: "What the census showed, and where the facts pile up.", start: "cover" },
    { description: "How the facts multiply, and what the merged rule changed.", start: "one-point" },
    { description: "The mistakes, and what the pass changed.", start: "mistakes" },
    { description: "The second regression, the results, and what prevents the kind.", start: "second" },
  ],
};
export default deck;
