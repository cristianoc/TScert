/* The gap-priorities deep dive: where TScert's proofs of its own code fail,
 * from the diagnostic census, the small sources made for those failures,
 * and the causes by priority, each closed one with how it was closed.
 * Built with the deck kit (`make deck NAME=gap-priorities`). */
import {
  bullets, card, cards, code, color, cover, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** A case's name, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
const trust = status("trust", "trust change");
const gap = (...names: string[]): string => `${status("gap", "gap")} ${names.map(c).join(", ")}`;
const neg = (...names: string[]): string => `${status("neg", "refused, rightly")} ${names.map(c).join(", ")}`;
const verifies = (...names: string[]): string => `${status("ok", "verifies")} ${names.map(c).join(", ")}`;
const noCase = status("gap", "no case");
const probe = `${noCase}; a probe reproduces it`;
const unproven = `${noCase}; no probe reproduces it`;
const closedBy = (commit: string, route: string): string => `${status("ok", "closed")} ${commit}, ${route}`;
const narrowed = (commit: string): string => `${status("gap", "narrowed")} ${commit}`;

/** A cause's slide: its site's code, then why it is refused, what proving
 * it needs and what that would trust. */
function cause(id: string, label: string, title: string, o: {
  note: string; source: string[]; why: string; todo: string; trust: string;
}): Slide {
  return slide(id, {
    label, title, gap: 18, note: o.note,
    body: code(o.source) + bullets([point("Why it is not proven", o.why), point("What proving it needs", o.todo), point("What it would trust", o.trust)]),
  });
}

const prio: [string, string, string, string, string][] = [
  ["1", "An optional field read on a parameter defaulted {}", "2,963", "1", probe],
  ["2", "A closure collecting a rest array, no result type", "812", "7", `${noCase}; a rewrite`],
  ["3", "One arm's writable array at a field of the wider union", "792", "10", gap("blocker-flat-map-narrow-field")],
  ["4", "new Set(s ?? []), s a ReadonlySet", "780", "29", probe],
  ["5", "A node used as an import after ts.isImportDeclaration", "758", "26", `${neg("invalid-compiler-api-js-import-guard")}; a repair`],
  ["6", "A map whose callback has an effect, then a call on it", "490", "11", probe],
  ["7", "An annotated callback on a union of node arrays", "394", "1", unproven],
  ["8", "An array literal spreading a map that builds records", "393", "2", unproven],
  ["9", "A member read after \"k\" in x on a union", "392", "8", neg("invalid-in-union-read")],
  ["10", "A spread overriding a nested field, {...f, type: {...}}", "352", "1", probe],
];

const more: [string, string, string, string, string][] = [
  ["11", "A find callback calling a function a field holds", "300", "1", probe],
  ["12", "Object.values of a record spread into an array literal", "229", "5", `${probe}; ${gap("spread-readonly-map-values-refused")}`],
  ["13", "A spread of an unknown narrowed to an object, { ...v }", "200", "5", probe],
  ["14", "a &amp;&amp; f(a), a an object or null, read in a template", "175", "5", probe],
  ["15", "A write that may add a key to an object another reference holds", "139", "12", verifies("blocker-loop-key-adding-write") + ", another site"],
  ["16", "A contextual type no declaration states", "132", "2", "cases in cases.mts"],
  ["17", "An async arrow's awaited result, its resolution not established", "129", "3", noCase],
  ["18", "A decoder's closing assertion, return v as T", "127", "5", `${neg("invalid-decoder-closing-assertion")}; a repair`],
  ["19", "Node's spawn, and a checker query on a namespace", "124", "2", noCase],
  ["20", "A dictionary read at a key Object.prototype may own", "122", "4", neg("index-signature")],
];

const lastTen: [string, string, string, string][] = [
  ["1. A member read on a let narrowed by two compiler guards", "2,798 · 2", closedBy("81d501f", `support, ${trust}`), verifies("blocker-let-guard-import-specifier")],
  ["2. A callback claimed outside its annotation", "1,415 · 11", narrowed("3cac8c3"), "10 of 11 now at 2, 6, 10 or verified; 6 functions, 5 new; below 20"],
  ["3. A closure capturing a for loop's let", "820 · 28", closedBy("3ae274c", "support"), verifies("for-let-capture")],
  ["4. Grouped switch cases returning at one site", "780 · 30", closedBy("d88723f", "support"), verifies("blocker-recursive-union-join")],
  ["5. A union met with one arm's discriminant", "766 · 11", closedBy("1ba2759", "support"), verifies("blocker-intersection-discriminant")],
  ["6. A closure reading a later, unannotated let", "688 · 25", closedBy("e9e9c3b", `support, ${trust}`), verifies("early-let-literal")],
  ["7. A member read after \"k\" in x on a union", "620 · 2", narrowed("874bdf8"), "its 2 sites closed; others, cause 9"],
  ["8. A union's record literal with a conditional spread", "387 · 2", closedBy("b7f78d0", "support"), verifies("blocker-spread-literal-discriminant")],
  ["9. A decoder's closing assertion", "335 · 4", narrowed("a5caf19"), "2 decoders repaired; 2 others, cause 18"],
  ["10. A class declared inside a function", "236 · 4", closedBy("97c4f17", `support, ${trust}`), verifies("blocker-local-class")],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which causes to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and many functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and reduces each cause to a small source. Part 2 shows what happened to the ten causes the last version of this deck ranked first, seven of them closed, and ranks the causes left by how much code they block.",
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert works, in three cards", gap: 28,
    body: cards([
      card("Verified, refused", "TScert verifies a function when it proves it safe: every value it reads, writes or returns has its declared type. Otherwise it refuses it, naming a location and a reason. The first stage, the <b>gate</b>, reads the TypeScript source and refuses what lies outside the language TScert admits; the <b>type reader</b> reads annotations and library declarations; the <b>producer</b> proposes a type for each expression, a <b>claim</b>; the later stages search for a proof of those types and check it."),
      card("Contract", "TScert's reviewed description of code it does not check itself: a function of JavaScript's standard library, of Node, or of TypeScript's compiler interface, each listed with its exact declaration and audited by hand. A contract is an assumption the result rests on: adding one widens what TScert trusts. A library global with no contract is refused; a function imported from a library with no contract is read through its declaration's written types."),
      card("Case, gap case", "A <b>case</b> is a small TypeScript file with the outcome TScert must give it, checked by the test suite (make suite). A <b>gap case</b> is one TScert refuses for want of a rule or a contract, though the program is safe: it turns into a verified case once the missing piece is added."),
    ]),
  }),
  slide("find", {
    label: "Part 1 · where proofs fail", title: "Two censuses of main (2026-10-30): 945fa80, then d373275", gap: 22,
    body: cards([
      stat("351 of 637", `functions of tools/ ${status("ok", "verified")} by the census of 945fa80, 3,300 of 15,319 statements (21.5%, measured); 305 of 604 and 16.5% at 5dd180f, the census the last version of this deck used`, "ok"),
      stat("542 of 596", "copies the diagnostic census of d373275 takes to their end (below); 46 stop at the 300 s limit of a stage, 14 of them before any refusal is reported; 8 at a refusal the traversal cannot replace by an opaque region (measured)"),
      stat("36.7%", "coverage with holes: 5,632 of the 15,326 statements of d373275 outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a copy, also called a slice) and run through TScert (make census). A refused function stops at its first reason. A copy may hold several functions."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified. This time most of what it reports past a function's first refusal is a failed proof search tried at one point of the code alone, a reason naming no construct."),
      point("Causes", "every refusal naming one construct counts. Each refused function also counts under its first refusal in the census of 945fa80: the source at the place that refusal names is read, in the copy of d373275, and the construct written there is the cause (a judgement). Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a small source", title: "Each heavy cause is reduced to a probe of a few lines", gap: 20,
    body: code(["// probe p10b: the shape of collectDeclarations's parameter (cause 1)",
      "export function f(options: { readonly diagnostic?: (r: string) => void } = {}): number {",
      "  if (!options.diagnostic) return 0;   // refused: missing field diagnostic",
      "  options.diagnostic(\"x\");",
      "  return 1;", "}"]) + bullets([
      point("A probe", "is the smallest source with the census site's refusal, run through TScert at d373275. Where a probe without one ingredient verifies, that ingredient is the cause; where every probe verifies, the cause is not established."),
      point("A case example", "is a probe made a case of the suite, its header naming the census functions it stands for. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("This census", "thirteen of the twenty heaviest causes (numbered on slide “The ten causes”) have no case of their own (cause 12's gap case is of a related spread, of a map's values). Probes reproduce eight of them (causes 1, 4, 6, 10–14); for causes 7 and 8 every probe tried verifies; cause 2 is a rule TScert's code is to meet (slide “Code to change”); causes 17 and 19 have no probe yet. Writing the cases is the next step."),
    ]),
  }),
  slide("round", {
    label: "Part 2 · since the last version", title: "The last version's ten causes: seven closed, three narrowed", gap: 14,
    body: table(["Cause at 5dd180f, the last version", "At 5dd180f", "Status, by", "Cases"], lastTen, [38, 10, 24, 28], { compact: true }) + bullets([
      "Statements · functions at 5dd180f; last column's causes: slide “The ten causes”; routes: “Eight routes”; trust change: a new or wider contract.",
    ]),
  }),
  slide("closed-more", {
    label: "Part 2 · since the last version, continued", title: "Fifteen smaller causes closed, and where the closed ones' functions stop now", gap: 16,
    body: table(["Cause at 5dd180f", "At 5dd180f", "Closed by"], [
      ["An annotated binding pattern; a callback relying on every(guard)", "218 · 9; 175 · 5", `d5903d4; 385907f, ${trust}`],
      ["A function a record field holds, passed to map", "139 · 14", "0cbaaaa"],
      ["sort of filter's fresh result; find's guard overload", "82 · 5; 73 · 5", `6b29e45, ${trust}; 40f0365`],
      ["Joins of host claims: residual join, parent loop", "70 · 3; 14 · 2", "3e77ea5, f80228c"],
      ["A map callback's literal result; a for...of loop's separation", "61 · 3; 46 · 1", "adb122b; b1b9110"],
      ["A loop with no exit: its completion, a closure's result", "17 · 1; 22 · 1", "97c2061"],
      ["Compiler node subtypes: a token, a generic member, a type node", "16 · 1; 9 · 1; 14 · 2", "43e7ce6; 52f8d0d, a repair"],
      ["A map callback reading getText on a binding name", "4 · 1", "3cac8c3"],
    ], [52, 20, 28], { compact: true }) + bullets([
      "All by route 1, support, but the type node: kind 234 is no TypeNode, so the refusal was right and the code tests the node's kind (route 3, a repair).",
      point("Where the functions stop now", "several of this census\'s causes (numbered on slide “The ten causes”) are sites the closed causes hid (read in the copies): collectDeclarations at cause 1, the type-term.mts copies at cause 4, expr and its copy at cause 3, classBody at cause 8. Seventeen functions verified at 5dd180f are refused by the census of 945fa80; each verifies on its copy at f80228c, a commit between 945fa80 and d373275 (WORK.md), and this diagnostic census checks 16 of them with no refusal."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · causes by priority, diagnostic census at d373275", title: "The ten causes that block the most code", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [5, 47, 11, 10, 27], { compact: true }) + bullets([
      "A function blocked by several causes counts under each; statements and functions are measured. Causes 2 and 5 are slide “Code to change”; causes 3, 7, 8: slide “Three causes without a rule yet”.",
      point("Judgements", "every cause of this slide but 7 and 9 counts its functions by the census's first refusal, read at its site (slide “Two censuses”); the diagnostic runs of causes 1, 2, 3 and 8, and of cause 5's functions of fragment-statements.mts, stop at the 300 s limit before any refusal."),
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · causes by priority, continued", title: "Causes 11–20, by statements", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], more, [5, 50, 11, 10, 24], { compact: true }) + bullets([
      point("Refusals naming no construct", "93 functions, 1,285 statements, meet no cause; 267 refused functions, 11,759 statements, in all at d373275 (measured): 945fa80's 286 less the 17 of slide “Fifteen smaller causes closed”, each verified on its copy at f80228c, and 2 the diagnostic census checks with no refusal."),
    ]),
  }),
  slide("routes", {
    label: "Part 2 · how a refusal is decided", title: "Eight routes, the first that works at acceptable cost", gap: 16,
    body: table(["Route", "When it applies"], [
      ["1. Support", "a rule or contract admits the construct: it has useful reach in the census and a proportionate implementation"],
      ["2. A runtime check", "an executable check establishes the whole property, also after later writes; checking a value's shape says nothing of what code writes"],
      ["3. A repair", "the refusal exposes a defect in TScert's code, which changes"],
      ["4. Avoidance", "support is costly, the construct rare, and a rewrite is observationally equivalent; the construct stays refused"],
      ["5. A host boundary", "a necessary operation on an external package moves to the smallest module, whose functions take only values that package makes"],
      ["6. A trusted unit", "the project's owner approves exempting a narrow unit of TScert's code from checking, reported with its contract; never a fallback"],
      ["7. A proof", "a proof in Lean, the proof assistant TScert's checker is proved in, where the model of JavaScript it needs exists or has wider value"],
      ["8. The refusal stays", "no route works at acceptable cost; the census reports it"],
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”, which also records each repair, avoidance and host boundary. Of the 22 causes closed this round, 21 took route 1, five of them with a trust change; one closed as a repair."]),
  }),
  cause("defaulted-options", "Cause 1 · 2,963 statements, 1 function", "An optional field read on a parameter defaulted {}", {
    note: `${noCase}: probes p10 and p10b reproduce it (measured)`,
    source: ["// declaration-graph.mts, collectDeclarations (l.826)", "… options: { …; diagnostic?: (pos: Span, reason: string) => void; … } = {}): DeclarationDocument {",
      "  const recover = (pos: Span, error: unknown): void => {", "    if (!options.diagnostic) {   // refused: missing field diagnostic", "      …"],
    why: "options is annotated with a record of optional fields and defaulted to {}. The producer reports diagnostic a missing member of options (the census's first refusal; the diagnostic run stops at the 300 s limit). A five-line source with the same parameter is refused alike, with or without the closure, and verifies without the default = {} (measured): the default decides it.",
    todo: "read a defaulted parameter at its annotation, the default checked against it (route 1, a rule); or a rewrite at the one site (route 4).",
    trust: "nothing: the default {} meets the annotation, whose fields are all optional.",
  }),
  slide("repairs", {
    label: "Causes 2 and 5 · 1,570 statements, 33 functions", title: "Code to change: two refusals by TScert's own rules", gap: 18,
    note: `cause 2 ${noCase}; cause 5 ${neg("invalid-compiler-api-js-import-guard")}`,
    body: code(["// fragment-parse.mts l.1691 (lowerFile and the 6 functions calling it), cause 2",
      "const add = (...names: string[]) => { firstAsync ??= node; names.forEach(name => intrinsicNames.add(name)); };",
      "// fragment-statements.mts l.361 (25 functions), guard-closure.mts l.64, cause 5",
      "if (ts.isImportDeclaration(st) && importedNames(st).includes(id.text)) return null;"]) + bullets([
      point("Why they are refused", "a closure collecting a rest array is checked at the signature its annotations state, and this one states no result type (cause 2): a rule of TScert's checker, not a wrong value. In TScert\'s contract of the compiler interface (81d501f), the guard ts.isImportDeclaration also admits a JSDoc @import node, of kind 346, with ImportDeclaration\'s members; importedNames takes an ImportDeclaration, which such a node is not, so under that contract the code could pass it a wrong value and the refusal is right (cause 5)."),
      point("What closing needs", "cause 2: route 4, avoidance, the result annotation : void, which changes nothing the code computes. Cause 5: route 3, a repair, a test of the node\'s kind in place of the guard, as 52f8d0d did for a type node and an import; it changes the result only for a kind-346 node."),
      point("What it would trust", "nothing."),
    ]),
  }),
  cause("set-default", "Cause 4 · 780 statements, 29 functions", "new Set(s ?? []), s a ReadonlySet: its element claimed never", {
    note: `${noCase}: probe p5b reproduces it (measured)`,
    source: ["// type-term.mts l.560 (29 functions of type-term.mts)", "const expandingAliases = new Set(scope.expandingAliases ?? []);   // scope.expandingAliases?: ReadonlySet<…>",
      "expandingAliases.add(alias);   // refused: no rule derives this invoke at Set<never>"],
    why: "the set is built from a ReadonlySet or, when it is absent, an empty array; the producer claims it a Set of never, so adding an alias is refused. Copies of type-term.mts run at d373275 stop there (measured); a five-line source with a ReadonlySet is refused alike, and with an optional array in its place verifies (measured). The copies reached this site once d88723f closed grouped switch cases.",
    todo: "infer the Set's element from both operands of ?? (route 1, a rule); or new Set&lt;TypeAliasDeclaration&gt;(…) at the one site (route 4).",
    trust: "nothing.",
  }),
  cause("effectful-map", "Cause 6 · 490 statements, 11 functions", "A map whose callback has an effect, then a call on its result", {
    note: `${noCase}: probes p8c and p4b reproduce it (measured)`,
    source: ["// type-probe.mts l.211 (makeProbe): the callback calls a method", "JSON.stringify((symbol?.declarations ?? []).map(d => { const node = d.resolve(); … })",
      "  .map(d => JSON.stringify(d)).sort());",
      "// claim-text.mts l.137 (10 functions): typeText writes state", "atom.args.map((t) => typeText(t, state)).join(\", \")"],
    why: "where the callback calls a method or writes an object, the search finds no proof that the map's result, claimed an Array of one element type, meets the ReadonlyArray of another element type that the next call requires (measured); why the element types differ is not established. Similar sources whose callback only reads a field verify (measured).",
    todo: "a case example from the probe, then the rule it shows missing: what the callback's effect may change of the map's result, a fresh array no other reference holds.",
    trust: "not known until the rule is established.",
  }),
  slide("open-three", {
    label: "Causes 3, 7 and 8 · 1,579 statements, 13 functions", title: "Three causes without a rule yet", gap: 18,
    note: `cause 3 ${gap("blocker-flat-map-narrow-field")}; causes 7 and 8 ${unproven}`,
    body: code(["// fragment-expressions.mts l.243 (expr and the 9 functions sharing its copy), cause 3",
      "const fields = parts.flatMap((p) => p.spread !== undefined ? [] : [p]);   // held at a field of the wider union",
      "// declaration-graph.mts l.5874 (collect), cause 7",
      "part.members.some((m: Node) => m.getText(part.getSourceFile()).trim() === entry.text)",
      "// fragment-classes.mts l.791 (classBody, classStmt), cause 8",
      "parts: [{ spread: derivedBase }, ...fields.map(({ name, e }) => ({ name: …, e }))]"]) + bullets([
      point("Cause 3", "an array of one arm of a union, writable, is held where an array of the whole union is expected; a write through the wider view could break the narrower one, so the refusal is right under TScert's rule, though the program is safe, since nothing else holds the array: a gap. Closing needs the array claimed at the wider element where nothing else holds it, or a rewrite (945fa80)."),
      point("Causes 7 and 8", "an annotated callback on a class's or an interface's members (per-arrow claims do not match), and an array literal spreading a map that builds records. Probes of both shapes verify (measured): the construct is not established, and a probe over the compiler's own types comes first."),
    ]),
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What comes next: repairs, cases, then rules", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. Changes of TScert's own code: causes 2 and 5, and the two other decoders of cause 18", c("invalid-compiler-api-js-import-guard"), status("ok", "none")],
      ["2. Case examples from the probes of causes 1, 4, 6, 10–14", "the eight probes of this round", status("ok", "none")],
      ["3. Rules: the defaulted parameter (1), the Set (4), the spread merges (10, 13); the effectful callback (6)", "", status("gap", "none expected; 6 not known")],
      ["4. Causes 3, 7 and 8, once a probe over the compiler's types shows the cause", c("blocker-flat-map-narrow-field"), status("gap", "not known")],
    ], [56, 28, 16]) + bullets([
      "The order follows the census process: changes of TScert's own code first, then the case examples, then the gap cases in the order of the code they block.",
      "The census and the diagnostic census, run once on main after these merges, measure what each gained.",
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert's proofs fail",
  slides,
  sections: [
    { description: "Where proofs fail, from the diagnostic census, and the small sources made from it.", start: "cover" },
    { description: "The causes by priority: what closed since the last version, and what closing the rest needs.", start: "round" },
  ],
};
export default deck;
