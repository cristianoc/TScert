/* The gap-priorities deep dive: where TScert's proofs of its own code fail,
 * from the diagnostic census, the case examples made for those failures,
 * and the cases by priority, each closed one with how and why it was
 * closed. Built with the deck kit (`make deck NAME=gap-priorities`). */
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
const closedBy = (commit: string, route: string): string => `${status("ok", "closed")} ${commit}, ${route}`;

/** A cause's slide: its case's code, then why it is refused, what proving
 * it needs and what that would trust, or, for a closed one, how it was
 * closed. */
function cause(id: string, label: string, title: string, o: {
  cases: string; source: string[]; why: string; todo: string; trust: string;
  closed?: { status: string; how: string }; note?: string; labels?: string[];
}): Slide {
  const labels = o.labels ?? (o.closed ? ["Why it was refused", "How it was closed, and why so", "What it trusts"]
    : ["Why it is not proven", "What proving it needs", "What it would trust"]);
  return slide(id, {
    label, title, gap: 18,
    note: o.note ?? (o.closed ? o.closed.status : `${status("gap", "gap")} ${o.cases}`),
    body: code(o.source) + bullets([point(labels[0] ?? "", o.why), point(labels[1] ?? "", o.closed ? o.closed.how : o.todo), point(labels[2] ?? "", o.trust)]),
  });
}

const prio: [string, string, string, string, string][] = [
  ["1", "A member read on a let narrowed by two compiler guards", "2,798", "2", noCase],
  ["2", "A callback over compiler nodes, xs.find(n => …)", "1,415", "11", noCase],
  ["3", "A closure capturing a for loop's let", "820", "28", gap("for-let-capture-refused")],
  ["4", "Grouped switch cases returning at one site", "780", "30", gap("blocker-recursive-union-join")],
  ["5", "A union met with one arm's discriminant (&amp;)", "766", "11", noCase],
  ["6", "A closure reading a later, unannotated let", "688", "25", noCase],
  ["7", "A member read after \"k\" in x on a union", "620", "2", noCase],
  ["8", "A union's record literal with a conditional spread", "387", "2", noCase],
  ["9", "A decoder's closing assertion, return v as Labels", "335", "4", noCase],
  ["10", "A class declared inside a function", "236", "4", gap("blocker-local-class")],
];

const more: [string, string, string, string, string][] = [
  ["11", "An annotated binding pattern", "218", "9", gap("blocker-annotated-pattern")],
  ["12", "JSON.stringify of a record type (it may own toJSON)", "213", "16", neg("invalid-json-stringify-record")],
  ["13", "A callback relying on an earlier every(guard)", "175", "5", gap("blocker-every-promise")],
  ["14", "A function a record field holds, passed to map", "139", "14", gap("blocker-callable-field-callback")],
  ["15", "A write that may add a key to an object another reference holds", "139", "12", verifies("blocker-loop-key-adding-write") + " (a local's own object); none of the 12"],
  ["16", "A contextual type no declaration states", "132", "2", "cases in cases.mts"],
  ["17", "An async arrow's awaited result, its resolution not established", "129", "3", noCase],
  ["18", "Node's spawn, and a checker query on a namespace", "124", "2", noCase],
  ["19", "A method read off its object, passed on with .bind or .call", "122", "5", gap("method-extraction-refused")],
  ["20", "A dictionary read at a key Object.prototype may own", "120", "3", neg("index-signature")],
];

const roundSix: [string, string, string, string][] = [
  ["A map callback's record, typed by a let", "387 · 2", closedBy("68b3ed3", "support"), verifies("blocker-callback-literal-union-receiver")],
  ["A numeric key not proved an array index", "112 · 2", closedBy("65d224c, 8892831", `support, ${trust}`), verifies("blocker-compiler-api-field-guard") + "; " + gap("blocker-array-index-of-write")],
  ["An array pattern, no array contract", "55 · 2", `${status("ok", "closed")} 3be9e73, read as knock-ons`, verifies("array-pattern-first-form")],
  ["An assignment to a module's let", "8 · 1", closedBy("cba5539", `support, ${trust}`), verifies("parameter-default-written")],
  ["selectGlobal's read only.binders", "346 · 1", closedBy("ead7ecb", "support"), verifies("blocker-distinct-map-values")],
  ["A field holding an object or null, reread", "114 · 2", `${status("gap", "open")} bdd3e02, 8506864, d0b0057`, verifies("blocker-aliased-guard")],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and many functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and turns each cause into a small case example. Part 2 shows how five of the six causes the last version of this deck left open were closed, what two changes of this round cost, and ranks the open causes by how much code they block.",
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
    label: "Part 1 · where proofs fail", title: "Two censuses of main at 5dd180f (2026-10-29)", gap: 22,
    body: cards([
      stat("305 of 604", `functions of tools/ ${status("ok", "verified")} by the census, 2,408 of 14,638 statements (16.5%, measured); 303 of 602 and 16.6% at c62a911, the census beside the diagnostic census at acd7436 the last version of this deck used`, "ok"),
      stat("503 of 563", "copies the diagnostic census takes to their end (below); 49 stop at the 300 s limit of a stage, 29 of them before any refusal is reported; 11 at a refusal the traversal cannot replace by an opaque region (measured)"),
      stat("32.0%", "coverage with holes: 4,679 of 14,638 statements outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a copy, also called a slice) and run through TScert (make census). A refused function stops at its first reason. A copy may hold several functions."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified."),
      point("Causes", "every refusal naming one construct counts, at whatever stage. Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number. A function whose diagnostic run reports only reasons naming no construct (a failed search), or none before the limit, counts under its first refusal in the census: the source at the place that refusal names is read for the construct there (a judgement)."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example, where one is found", gap: 20,
    body: code(["// the source that the census site at fragment-classes.mts l.713 (slide “Cause 8”) reduces to",
      "type E = { readonly k: \"id\"; readonly name: string }",
      "  | { readonly k: \"alloc\"; readonly fields: readonly { name: string; e: E }[]; readonly proto?: E };",
      "export function link(name: string, proto: E | null): E {",
      "  const l: E = { k: \"alloc\", fields: [{ name: \"message\", e: { k: \"id\", name } }], ...(proto ? { proto } : {}) };",
      "  return l;   // refused at l's annotation: the literal's k is claimed a string", "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from a census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("This census", "seven of the ten heaviest causes, numbered on slide “The ten causes”, have no case. The source above, not yet a case of the suite, reproduces cause 8, and without its spread it verifies; a four-line source reproduces cause 5 (measured). For causes 1 and 2 no small source is found yet. Writing these cases is the next step."),
    ]),
  }),
  slide("round", {
    label: "Part 2 · since the last version", title: "The six causes left open by the last version: five closed, one open", gap: 16,
    body: table(["Cause at acd7436, the last version", "At acd7436", "Status, by", "Cases"], roundSix, [34, 11, 27, 28], { compact: true }) + bullets([
      "Statements · functions, measured at acd7436; routes: slide “Eight routes”.",
      point("Where those functions stop at 5dd180f", "classBody and classStmt at cause 8 of slide “The ten causes”, selectGlobal at cause 2, recoverGate at Object.defineProperties (no contract). 3be9e73 read the array-index and array-pattern refusals as following earlier ones: in forInEntryReads, a narrowing lost across a for...of loop (next slide)."),
      point("The open one", "readDiagnostic's callback calls an import whose declaration states no effect, so it may change the tested field (bdd3e02). 8506864 keeps a guard's narrowing past a middle test, as in its !isRecord(claim) || !Array.isArray(available) || …; d0b0057, a guard's answer in a constant (assignedSteps)."),
    ]),
  }),
  cause("for-of", "Closed by 65d224c and 8892831 · cases of the round", "Closed: a field's narrowing kept across a for...of loop", {
    cases: "", source: ["// blocker-field-narrowing-for-of: verified (8892831)",
      "type Statement = { k: \"block\"; statements: readonly number[] } | { k: \"empty\" };",
      "export function count(node: { readonly statement: Statement }): number {",
      "  if (node.statement.k !== \"block\") return 0;",
      "  let n = 0;",
      "  for (const s of node.statement.statements) n += s;",
      "  return n + node.statement.statements.length;   // read at the narrowed type",
      "}"],
    why: "forInEntryReads tests node.statement, a compiler node's field, loops over its statements and rereads it. The producer forgot every known field at the loop, a compiler node's fields included, which do not change (65d224c). For a plain record, the loop calls its iterator's step at each iteration, and the step's declared effect let it change any location, so no fact about a field survived the loop (8892831).",
    todo: "",
    trust: `${trust} (8892831): the array iterator is a fresh object whose step changes only the iterator's own locations; 65d224c also adds a contract of Object.getOwnPropertyDescriptors, ${trust}.`,
    closed: { status: verifies("blocker-compiler-api-field-guard", "blocker-field-narrowing-for-of"),
      how: "route 1, support. 65d224c: the producer keeps a compiler node's fields across the loop. 8892831: the iterator is a new object, and its step changes only the iterator's own locations; inside the loop, TScert claims that the iterator shares no location with the fields of the values that exist before the loop, and checks that claim where the loop is entered and repeated. A write of the field in the body, in a closure and in a callback stays refused.",
    },
  }),
  slide("lost", {
    label: "Part 2 · a function lost, and slower runs", title: "What 8892831 and 65d224c cost the census", gap: 18,
    note: `${status("gap", "regression")} diagnostic.mts#knowledge`,
    body: code(["// diagnostic.mts, knowledge (l.307): verified at c62a911, refused at 5dd180f",
      "for (const p of f.partners) {",
      "  if (!Array.isArray(p) || p.length !== 2) throw Error(\"invalid separation partner\");",
      "  nat(p[0]); keys(p[1]);",
      "}"]) + bullets([
      point("The lost function", "knowledge loops over an array a field holds, after Array.isArray tested the field, and its body tests each element. At a path entering that loop's body the search finds no proof of the claims there; the claims it reports missing include claims that two values share no location, the kind 8892831 adds inside a loop (read in the diagnostic output). A ten-line source of this loop verifies at 65d224c and is refused at 8892831 (measured). The source of knowledge is the same at both commits."),
      point("Slower runs", "seven copies of fragment-parse.mts (lowerFile and its callers) exceed the 1200 s limit of a whole run. A run may use the checked types of a function of another module; where the search refuses them, the run drops that function and proposes and searches again, a round of about 130 s here: 5 rounds at c62a911, more than 7 at 5dd180f, the added rounds dropping functions of fragment-support.mts (measured). 65d224c adds the rounds, measured on letPatternOf, verified both times: 1 search at 8506864, the code commit before it, 4 at 65d224c. For fragment-parse.mts it is a judgement."),
      point("Same work", "on copies where a stage ran as many times in both censuses, its CPU changed by −8.0% (producer), +6.7% (search) and +7.6% (check), measured."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at 5dd180f", title: "The ten causes that block the most code", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [5, 51, 11, 10, 23]) + bullets([
      "A function blocked by several causes counts under each; statements and functions are measured. Causes 3 and 6: slide “Code refused in the gate's own placement”.",
      point("Judgements", "causes 1, 5, 7, 8, 9, four of cause 2's functions and 29 of cause 4's count by the census's first refusal (slide “Two censuses”), seven of cause 2's by that at c62a911 (slide “What 8892831 and 65d224c cost”); cause 6 is told apart from another construct of its reason by function."),
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · cases by priority, continued", title: "Causes 11–20, by statements", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], more, [5, 50, 11, 10, 24], { compact: true }) + bullets([
      point("Refusals naming no construct", "99 functions, 1,904 statements, meet no cause (measured), the largest collect (394) and checkedGuards (173); 299 refused functions, 12,230 statements, in all (measured)."),
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”, which also records each repair, avoidance and host boundary. Of the five causes closed this round, four took route 1, two of them with a trust change (cba5539; 65d224c and 8892831); the fifth was read as refusals following earlier ones."]),
  }),
  cause("let-guard-narrowing", "Cause 1 · 2,798 statements, 2 functions", "A member read on a let narrowed by two compiler guards", {
    cases: "", note: `${noCase}: the same shape over the program's own types verifies (measured)`,
    source: ["// declaration-graph.mts l.317–322 (collectDeclarations, statementsOnPath)", "let node: Node | undefined = symbol.declarations[0]?.resolve();",
      "while (node && !ts.isImportDeclaration(node) && !ts.isExportDeclaration(node) && !ts.isSourceFile(node))", "  node = node.parent;",
      "if (node && (ts.isImportDeclaration(node) || ts.isExportDeclaration(node))) {", "  out.push(node);", "  if (node.moduleSpecifier) starExports(node.moduleSpecifier);   // refused: missing field moduleSpecifier", "}"],
    why: "after the test, node is an import or an export declaration, both of which declare moduleSpecifier, yet the producer reports it a missing member (measured in the census). A source of the same shape over three record types and two guards of the program verifies, so the cause lies with the compiler's guards or node types; which one is not established.",
    todo: "first a case example that reproduces the refusal over the compiler's types; then the rule or the contract entry it shows missing.",
    trust: "not known until the cause is established.",
  }),
  cause("node-callback-signature", "Cause 2 · 1,415 statements, 11 functions", "A callback over compiler nodes, claimed outside its annotation", {
    cases: "", note: `${noCase}`,
    source: ["// fragment-parse.mts l.2209 (lowerFile and 6 functions calling it)", "const node = [...importNodes, ...localNodes, ...globalNodes].find(n =>",
      "  n.getStart(source) === root.binding.span[0]) ?? first;", "// declaration-graph.mts l.4633 (selectGlobal, globalFunction):", "//   overloads.find(o => resolved && o.pos === resolved.pos && …)"],
    why: "the arrow n => … has no annotation, so its type is the one find's declared callback parameter gives it; the search rejects the type the producer claims for the arrow as lying outside that one (“closure signature claim is outside the source annotation”). The eleven functions meet four sites, each a callback over an array of compiler nodes. selectGlobal (346 statements) joins at its find, past the read only.binders that ead7ecb closed. What makes the claim differ is not established.",
    todo: "a case example over compiler nodes, then the rule or repair it shows missing.",
    trust: "not known until the cause is established.",
  }),
  slide("added-code", {
    label: "Cause 6 · 688 statements, 25 functions; cause 3 · 723 of its 820, 26 of its 28", title: "Code refused in the gate's own placement of declarations", gap: 18,
    note: `cause 3 ${gap("for-let-capture-refused")}; cause 6 ${noCase}`,
    body: code(["// fragment-statements.mts, functionPlacement (l.660), code added by e499515",
      "for (let changed = true; changed;) {", "  changed = false;", "  live.forEach((s, i) => { … placed.set(f, at); changed = true; … });", "}",
      "// fragment-statements.mts, markEarly (l.808): visit, a closure declared above, reads statementStart",
      "let statementStart = -1;"]) + bullets([
      point("Why they are refused", "JavaScript gives each iteration of a for loop its own copy of the loop's let, and TScert binds it once, so a closure capturing it is refused (cause 3). A let a closure may read before its declaration has run must state its type (cause 6). Both are met by every copy of fragment-statements.mts that reaches these two functions."),
      point("What closing needs", "a rewrite of each site, route 4, avoidance (a judgement): the loop over a let declared outside it, and the annotation let statementStart: number. Neither changes what the code computes. Cause 3's two older sites, in guardClosure and freeOffsets (97 · 2), stay."),
      point("What it would trust", "nothing."),
    ]),
  }),
  cause("recursive-union-join", "Cause 4 · 780 statements, 30 functions", "Grouped switch cases returning at one site", {
    cases: "blocker-recursive-union-join",
    source: ["// type-term.mts, restRefusal (l.196); reached by 30 copies of type-term.mts", "switch (type.k) {", "  case \"parameter\": return `${REST_CONTRACT}: …`;   // … one case per kind",
      "  case \"array\": case \"union\": case \"reference\":", "    return REST_CONTRACT;   // refused: the incoming edge does not establish its claims", "  default: return `${REST_CONTRACT}: …`;", "}"],
    why: "type is a TypeTerm, a recursive union of records discriminated by k. Three case labels reach one return, and the search finds no proof that the claims at that return hold on every edge into it (measured; the case reproduces it).",
    todo: "join the knowledge of grouped case labels on a recursive union (route 1, a rule); or a rewrite at the one site, one return per label (route 4).",
    trust: "nothing.",
  }),
  cause("intersection-discriminant", "Cause 5 · 766 statements, 11 functions", "A union intersected with one arm's discriminant", {
    cases: "", note: `${noCase}: reproduced by a four-line source (measured)`,
    source: ["// fragment-expressions.mts l.1936, chainReads", "function chainReads(gate: Gate, at: Node, chain: Expr & { k: \"optional\" }): … {", "  …",
      "  const receiver = chain.receiver;   // refused: missing field receiver"],
    why: "Expr is a union of records discriminated by k; Expr &amp; { k: \"optional\" } is exactly its optional arm, which declares receiver. The producer does not select that arm from the intersection and reports receiver a missing member: expr (300 statements), binary (142), lambda (129) among the 11.",
    todo: "read the intersection of a discriminated union with one arm's discriminant as that arm (route 1, a rule); or a rewrite at the one site, the parameter typed by the arm's own name (route 4).",
    trust: "nothing: the intersection and the arm hold the same values.",
  }),
  cause("spread-literal", "Cause 8 · 387 statements, 2 functions", "A union's record literal with a conditional spread", {
    cases: "", note: `${noCase}: reproduced by the source of Part 1 (measured)`,
    source: ["// fragment-classes.mts l.713 (classBody, classStmt)",
      "const link: Expr | null = base?.error && heritage ? { k: \"alloc\", pos: …,",
      "  fields: [{ name: \"message\", e: … }, { name: \"name\", e: … }],",
      "  ...(proto ? { proto } : {}) } : null;   // refused at link's annotation"],
    why: "the literal is the alloc arm of Expr, a union of records discriminated by k. With the spread, the producer claims the literal at { k: string, … }, which no arm of Expr holds; the same literal without the spread verifies (measured). classBody and classStmt reached this site once 68b3ed3 closed their earlier refusal.",
    todo: "type a literal with a conditional spread at the arm its discriminant names (route 1, a rule); or a rewrite at the one site, two literals, one with proto and one without (route 4).",
    trust: "nothing.",
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What comes next: the regression, cases, then rules and rewrites", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. The function lost to 8892831: the loop's claim established where knowledge's loop enters", "", status("ok", "none")],
      ["2. Case examples for causes 1, 2, 5–9, each from its census site", "the sources of Part 1 and of cause 5; five to write", status("ok", "none")],
      ["3. Rewrites of the gate's placement code (cause 6, and 26 of cause 3's functions)", c("for-let-capture-refused"), status("ok", "none")],
      ["4. Rules or rewrites: grouped case labels (4), the discriminant intersection (5), the in test (7), the literal with a spread (8)", c("blocker-recursive-union-join"), status("ok", "none expected")],
      ["5. Causes 1 and 2, once their cases show the cause", "", status("gap", "not known")],
    ], [56, 28, 16]) + bullets([
      "The order follows the census process: what this round lost, then the case examples, then the rewrites of TScert's own code, then the gap cases in the order of the code they block.",
      "The census and the diagnostic census, run once on main after these merges, measure what each gained.",
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert's proofs fail",
  slides,
  sections: [
    { description: "Where proofs fail, from the diagnostic census, and the case examples made.", start: "cover" },
    { description: "The cases by priority: open ones, what closing needs; closed ones, how and why.", start: "round" },
  ],
};
export default deck;
