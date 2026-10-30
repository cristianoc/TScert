/* The lowerFile deep dive: where the run time of the census slice of
 * tools/fragment-parse.mts#lowerFile goes, stage by stage and inside the
 * producer, which part is proportional to the program and which part is
 * repeated work, the two repairs measured, and the designs proposed for the
 * rest. Built with the deck kit (`make deck NAME=lowerfile-time`). */
import {
  bullets, card, cards, code, columns, cover, inline, panel, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

/** Prose: `code` in backticks takes the code colour. */
const t = inline;

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · run time of one census slice",
    title: "Where lowerFile's 239 seconds go",
    text: "TScert checks type claims about TypeScript programs and is run on its own front end, one function at a time. Checking the function lowerFile of tools/fragment-parse.mts took 239 s, with no earlier result to reuse. This deck attributes that time to the steps of the check and, inside the slowest one, to what it repeats. Two repairs of data structures, which change no output, bring the check to 108 s. Of those, about 30 s follow the size of the program; of the producer's remaining 64 s, 30 s are measured repetition, and three designs are proposed for it. The next slide explains the words.",
  }),
  slide("terms", {
    label: "Words used in this deck", title: "A slice, its stages, and its outcome", gap: 22,
    body: cards([
      card("Slice, census, refusal", "A slice is one top-level function of TScert's front end (the folder tools/), copied into a file of its own with the definitions of its file it uses, and checked alone. The census checks every slice and records each one's outcome and the time of every step. A check ends verified, or in a refusal: the place where no proof of the proposed types was found, and why."),
      card("Stages", "A check runs separate programs, one after another. <b>parse</b>: TypeScript's compiler reads the slice and each module it imports into syntax documents. <b>lower</b>: Lean, a proof assistant, derives each function's control-flow graph. <b>propose</b>: an OCaml program, the producer, proposes a type, a claim, for every expression. <b>plan</b>: Lean decides which certified imports (slide “Import rounds”) the slice may use. <b>search</b>: Lean looks for a proof of the claims."),
      card("Empty store", "A cache keyed by a stage's exact inputs replays a stage it already holds. Every measurement here starts with it empty, so every stage runs. Times are of one check on a 12-core laptop, at commit ee0ed0e5 of the repository unless a slide says otherwise."),
    ]),
  }),
  slide("stages", {
    label: "Measured: census of ee0ed0e5, empty store, 2026-10-30", title: "One stage, propose, takes 190 of the 239 s", gap: 20,
    body: table(["Stage", "Runs", "Elapsed", "What a run reads"], [
      ["propose: the slice", "1", "133.3 s", "the slice: 5 functions, 30 MB of syntax with its 21 imported modules"],
      ["propose: imported modules", "27", "56.5 s", "one imported module, so that the slice may rely on what TScert proves of it"],
      ["parse, the 21 modules included", "1 + 29", "24.3 s", "the slice through TypeScript's compiler; 20.3 s of it reading the modules"],
      ["plan", "16", "11.0 s", "the slice's syntax and its list of certified imports"],
      ["search", "1", "7.5 s", "the proof search, which ends in the refusal"],
      ["lower", "22", "3.0 s", "the control-flow graphs of the slice and the modules"],
    ].map(r => r.map(t)), [27, 8, 12, 53]) + bullets([
      "The 6 extra module proposals and 14 of the 16 plans come from import rounds (slide “Import rounds”). Outcome, unchanged by everything in this deck: refused, “closure signature claim is outside the source annotation”, at one closure of lowerFile.",
      "In the census of the earlier commit 5dd180f, lowerFile and six functions calling it did not finish within the census's 1200 s limit for one check; at ee0ed0e5 lowerFile finishes in 239 s.",
    ]),
  }),
  slide("size", {
    label: "Measured: the slice's proposal", title: "What the 133 s proposal processes", gap: 22,
    body: cards([
      stat("735", t("statements in `lowerFile`, one function of the slice's 5; its control-flow graph has 325 nodes")),
      stat("52,660", "expression typings in the run, over the passes of slide “What the remaining 29 s repeat”"),
      stat("≈100", "bindings in an environment, the list of the names in scope with their types: locals, parameters and imported names (34.2 million bindings over 338,542 joins)"),
    ]) + bullets([
      point("How the producer types a function", t("in one pass it walks the function's control-flow graph, carrying an environment from node to node. Where two paths meet, such as the two arms of a conditional expression `c ? a : b`, it joins their environments: each binding of one path's environment is looked up by name in the other's, and the two types are united.")),
      point("Its inputs", t("29.8 MB of syntax (28.9 MB of it the imported modules' declarations), 10.8 MB of control-flow graphs (4.7 MB of them `lowerFile`'s); it writes 9.8 MB of claims.")),
    ]),
  }),
  slide("profile", {
    label: "Measured: sampling profiler, and a build counting each lookup", title: "93% of the slice's proposal is looking up names in lists", gap: 20,
    body: columns([
      bullets([
        point("Sampled", t("1 ms samples of the running proposal: 93% inside OCaml's `List.assoc_opt`, the standard lookup in a list of pairs, almost all of it comparing names.")),
        point("Counted", "the join's lookups (the two shown, and two more in the join and the function calling it) ran 34.2 million times each and visited 3.7 to 3.8 billion list cells each: about 110 cells per lookup."),
        point("Why", "an environment is a list, so a lookup walks it, and a join makes ≈100 such walks where a table answers each lookup directly."),
      ]),
      panel("The join, before, abridged (ocaml-producer/execution_analysis.ml)", code([
        "(* for each binding of before *)",
        "List.filter_map (fun (n,b) ->",
        "  match b, List.assoc_opt n left,",
        "           List.assoc_opt n right with",
        "  | ... -> Some (n, union l r)) before",
      ])),
    ], [58, 42]),
  }),
  slide("repairs", {
    label: "Two repairs, changing no output", title: "The same claims; the slice's proposal in a quarter of the time", gap: 18,
    body: cards([
      card("1 · A table for the join", t("Each environment of a join is indexed once by name (a hash table keeping the first binding of each name, which is what the list lookup finds), and every binding is looked up there. The joined environment is the same list, in the same order.")),
      card("2 · Uniting sorted lists by merging", t("A type is often a list of alternatives kept sorted without repeats. Uniting two such lists sorted their concatenation again; it now merges them in one pass when both are sorted, and sorts otherwise. The result is the same list.")),
    ], 2) + table(["Producer CPU, user time, on saved inputs", "ee0ed0e5", "repair 1", "repairs 1 and 2"], [
      ["the slice", "121.5 s", "33.8 s", "28.8 s"],
      ["module tools/type-probe.mts", "15.6 s", "14.6 s", "6.8 s"],
      ["module tools/type-term.mts", "9.7 s", "9.3 s", "7.2 s"],
      ["module tools/fragment-support.mts", "7.3 s", "7.4 s", "5.2 s"],
      ["module tools/library-modules.mts", "5.6 s", "5.8 s", "5.7 s"],
    ].map(r => r.map(t)), [46, 18, 18, 18]) + bullets([
      "Measured one after another, 2026-10-30; each output identical byte for byte to ee0ed0e5's. The whole check, empty store: 239 s → 108 s, propose 184.9 → 64.1 s of CPU, the same refusal. Library-modules spends its time elsewhere (next slide).",
    ]),
  }),
  slide("repeated", {
    label: "Measured: a timing build on the slice", note: "the producer with counters and timers added; the same claims", title: "What the remaining 29 s repeat", gap: 16,
    body: table(["Repetition", "Count", "Time"], [
      [t("**Entry environments recomputed.** To type a sub-expression, the producer reruns the evaluation of its whole statement from the start, to find the environment where that sub-expression begins."), "50,972 reruns over 1,879 statements (a statement at one graph node), 27 each", "19.1 of 29.4 s, 65%"],
      [t("**Passes over `lowerFile`.** The producer assumes what each function's calls may change (its effect), types every function, and repeats until no assumption grows: 2 effect rounds. In each, `lowerFile` is typed twice, the second time because the first found calls passing one of its closures more arguments than it declares, which the closure's type must then state."), t("4 passes of `lowerFile`"), "6.6 s outside the reruns, over the 4"],
      [t("**Types compared in full.** Two equal types built separately are compared part by part; the types here are unions of hundreds of TypeScript syntax-node types."), "12.2 million unions of two types", "not timed apart"],
    ], [52, 26, 22]) + bullets([
      t("In the modules the reruns take 0.8 of 6.6 s (type-probe), 2.6 of 7.0 s (type-term), 2.0 of 5.5 s (fragment-support) and 5.7 of 5.9 s (library-modules: 3,300 reruns over 61 statements, 2.44 million evaluation steps)."),
    ]),
  }),
  slide("rounds", {
    label: "Measured: census of ee0ed0e5, empty store", title: "Import rounds: one import dropped per round", gap: 20,
    body: bullets([
      point("Certified imports", "the slice may type a call of an imported function by what TScert proves of that function in its own module, instead of by its declared type alone. It may do so only where the slice and the module give the function the same signature. Before proposing the slice, the plan checks each such import; where it refuses one, the import is dropped, and the round starts again."),
      point("This slice", "14 rounds each drop one import; the 15th plan passes, the slice is proposed, and the search stage runs the plan once more to divide its work: 16 plans of 0.6–0.9 s, 11.0 s. Each plan reads the whole 30 MB syntax document."),
      point("Modules proposed again", t("a module's proposal depends on which of its own calls of other modules are still typed by certified imports, so a dropped import can change it; each round proposes again each module so changed: 27 proposals of 21 modules, tools/declaration-graph.mts five times at 1.8 s.")),
      point("Avoidable", "a plan that reports every import it refuses lets one round drop them all: an estimated 16 → 3 plans (−9 s), and about −5.5 s of the 8.8 s of repeated module proposals, since each changed module is still proposed once more. The outcome stays the same only if no refusal depends on another import being dropped, which the change would have to show."),
    ]),
  }),
  slide("verdict", {
    label: "Intrinsic or avoidable", note: "census after the repairs, 2026-10-30; shares from the timing build", title: "30 of the remaining 108 s follow the program; about half the producer's 64 s is repetition", gap: 16,
    body: table(["Part", "Time after the repairs", "Verdict"], [
      [t("the compiler reads the slice and 21 modules"), "20.2 s; 24.3 and 24.0 s in two earlier censuses, run-to-run variation on a shared machine", `${status("neutral", "proportional")}: TypeScript's reading of the source and its imports`],
      [t("one search, the lowering"), "9.4 s", `${status("neutral", "proportional")}: one proof attempt over the slice's graphs`],
      [t("the quadratic join and the re-sorting"), "propose CPU 184.9 → 64.1 s", `${status("ok", "repaired")} (slide “Two repairs”)`],
      [t("entry environments recomputed"), "30.2 s in the slice and 4 modules", `${status("principled", "avoidable")}: one evaluation per statement`],
      [t("the second effect round over `lowerFile`"), "2 of its 4 passes", `${status("principled", "avoidable")}: typed after its callees, one round suffices`],
      [t("16 plans, modules proposed again"), "≈15 s saved (estimated)", `${status("principled", "avoidable")} if refusals are independent`],
      [t("types compared part by part"), "not timed apart", `${status("principled", "avoidable")}: shared, numbered types`],
    ], [36, 24, 40], { compact: true }) + bullets([
      "“Proportional”: the cost follows the size of the program and what it imports, as one producer pass per function does; the measured reruns are 30.2 of the producer's 64.1 s, 47%, plus the repeated proposals.",
    ]),
  }),
  slide("designs", {
    label: "Proposed, not built", title: "Three designs for the producer, by expected gain", gap: 18,
    body: bullets([
      point("Entry environments in one evaluation", t("evaluate a statement once while typing it, in evaluation order, handing each sub-expression the environment the evaluation has reached. A rerun sees the claims typed so far, so the design must show it gives the environments the reruns give, or record the claims each step reads and rerun only when one changed. Expected: one evaluation per statement instead of 27 in the slice; estimated −18 s in the slice and −11 s in the four modules measured.")),
      point("Passes only where an assumption changed", t("type the functions callee before caller, in the order of the call graph, so a function is typed once its callees' effects are final; a recursive group is iterated alone. Expected: `lowerFile` typed in one effect round, 4 → 2 passes, an estimated −3.5 s once the first design lands; the closure pass stays.")),
      point("Shared, numbered types", "build each distinct type once and give it a number, so two types are equal exactly when their numbers are; union, join and lookup then compare numbers. Expected gain not measured; the largest change of the three, touching every module of the producer."),
      "With the first two and one import round, the producer's 64 s of CPU in this check would fall to an estimated 25 s, before the third; with the plans saved too, the check would take about 60 s, the compiler's 20 s and the search among them.",
    ]),
  }),
  slide("goal", {
    label: "Against the goal of one second per function", title: "What one second would take", gap: 22,
    body: cards([
      stat("239 → 108 s", `the check on an empty store, the same refusal (${status("ok", "measured")})`, "ok"),
      stat("20.2 s", "of the 108 are the compiler reading the slice and its 21 modules: every slice importing them pays it again on an empty store"),
      stat("≈25 s", `producer CPU once two designs and one import round land (${status("gap", "estimated")})`),
    ]) + bullets([
      "A census replays a module's reading, lowering and proposal from the store when another slice already ran them with the same inputs, so in a census a slice's own cost is close to its own stages.",
      "No step of this check is unexplained: each slide above attributes its time, and the 1200 s limit of the census of 5dd180f (slide “Stages”) is far away.",
      "One second for a 735-statement function needs the producer typing each expression once (the designs above) and a search proportional to the function: a target, not an estimate.",
    ]),
  }),
];

const deck: Deck = {
  title: "Where lowerFile's time goes",
  slides,
  sections: [
    { description: "Terms, and the stages of the check's 239 s.", start: "cover" },
    { description: "Inside the proposal: the profile, the two repairs, what it repeats.", start: "size" },
    { description: "Import rounds, the verdict, the designs and the goal.", start: "rounds" },
  ],
};
export default deck;
