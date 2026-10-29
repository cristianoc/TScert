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
const narrowedBy = (commit: string, route: string): string => `${status("ok", "narrowed")} ${commit}, ${route}`;

/** A cause's slide: its case's code, then why it is refused, what proving
 * it needs and what that would trust, or, for a closed one, how it was
 * closed; a narrowed one says what was closed and what stays open. */
function cause(id: string, label: string, title: string, o: {
  cases: string; source: string[]; why: string; todo: string; trust: string;
  closed?: { status: string; how: string; narrowed?: true }; note?: string; labels?: string[];
}): Slide {
  const labels = o.labels ?? (o.closed?.narrowed ? ["Why it was refused", "What was closed, and what stays open", "What it trusts"]
    : o.closed ? ["Why it was refused", "How it was closed, and why so", "What it trusts"]
    : ["Why it is not proven", "What proving it needs", "What it would trust"]);
  return slide(id, {
    label, title, gap: 18,
    note: o.note ?? (o.closed ? o.closed.status : `${status("gap", "gap")} ${o.cases}`),
    body: code(o.source) + bullets([point(labels[0] ?? "", o.why), point(labels[1] ?? "", o.closed ? o.closed.how : o.todo), point(labels[2] ?? "", o.trust)]),
  });
}

const prio: [string, string, string, string, string][] = [
  ["1", "A member read on a let narrowed by two compiler guards", "2,798", "2", noCase],
  ["2", "A callback over compiler nodes, xs.find(n => …)", "1,069", "10", noCase],
  ["3", "A closure capturing a for loop's let", "818", "28", gap("for-let-capture-refused")],
  ["4", "Grouped switch cases returning at one site", "780", "30", gap("blocker-recursive-union-join")],
  ["5", "A union met with one arm's discriminant (&amp;)", "764", "11", noCase],
  ["6", "A closure reading a later, unannotated let", "686", "25", noCase],
  ["7", "A member read after \"k\" in x on a union", "620", "2", noCase],
  ["8", "A map callback's record, typed by a let", "387", "2", noCase],
  ["9", "A decoder's closing assertion, return v as Labels", "335", "4", noCase],
  ["10", "A class declared inside a function", "236", "4", gap("blocker-local-class")],
];

const more: [string, string, string, string][] = [
  ["An annotated binding pattern", "218", "9", gap("blocker-annotated-pattern")],
  ["JSON.stringify of a record type (it may own toJSON)", "213", "16", neg("invalid-json-stringify-record")],
  ["A callback relying on the narrowing an earlier every(guard) gives", "175", "5", gap("blocker-every-promise")],
  ["A function a record field holds, passed to map", "139", "14", gap("blocker-callable-field-callback")],
  ["A write that may add a key to an object another reference holds", "139", "12", verifies("blocker-loop-key-adding-write") + " (a local's own object); none of these"],
  ["A contextual type no declaration states", "130", "2", "cases in cases.mts"],
  ["An async arrow's awaited result, its resolution not established", "129", "3", noCase],
  ["Node's spawn, and a checker query on a namespace", "124", "2", noCase],
];

const lastVersion: [string, string, string][] = [
  ["1. Omit&lt;I, K&gt; of an interface", "3,051 · 4", closedBy("916de07", "support")],
  ["2. A callback parameter typed at a type parameter not in scope", "2,704 · 1", closedBy("99224c2", "support")],
  ["3. The compiler enum TypePredicateKind", "2,704 · 1", closedBy("cdbef56", `a contract, ${trust}`)],
  ["4. An optional call of a method whose object is a call", "2,704 · 1", closedBy("ba56fa4", "support")],
  ["5. A declaration list of two destructuring patterns", "2,704 · 1", closedBy("faeefe4", "support")],
  ["6. ReturnType of a local function's typeof", "2,704 · 1", closedBy("3911301", "support")],
  ["7. Symbol's getExports and getMembers", "2,704 · 1", closedBy("cdbef56", `a contract, ${trust}`)],
  ["8. A union's arm read after a test through ?.", "1,168 · 9", closedBy("ba56fa4", "support")],
  ["9. A spread of a node list or an empty array", "781 · 7", closedBy("2eb94e2", "support")],
  ["10. A map callback returning a record literal", "780 · 31", narrowedBy("b73553a", "support; 387 · 2 left (8 of the table)")],
];

const further: [string, string, string, string][] = [
  ["A numeric key not proved an array index", "490 · 5", "112 · 2", narrowedBy("02fd760", "avoidance")],
  ["An array pattern over a value with no array contract", "431 · 3", "55 · 2", `${status("ok", "narrowed")} commit not attributed`],
  ["An assignment to a module's let, or its increment", "378 · 42", "8 · 1", narrowedBy("4e12c57", "support")],
  ["An object pattern's key spelled as a later local", "340 · 1", "none", closedBy("70dece7", "support")],
  ["A test of an optional never field as a discriminant", "320 · 1", "none", closedBy("8476774", "support")],
  ["A function declaration inside a function", "305 · 2", "none", closedBy("e499515", `support, ${trust}`)],
  ["A field holding an object or null, reread after a test", "299 · 8", "114 · 2", narrowedBy("c62a911", "support")],
  ["An imported class's type parameter default (API)", "245 · 13", "none", closedBy("a0b9cdd", "support and avoidance")],
  ["A record index at a key that is not a string", "239 · 1", "none", closedBy("02fd760", "a repair")],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and many functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and turns each cause into a small case example. Part 2 ranks those cases by how much code they block, shows for each cause closed since the last version how and why it was closed, and for the heaviest open ones what closing them needs.",
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert works, in three cards", gap: 28,
    body: cards([
      card("Verified, refused", "TScert verifies a function when it proves it safe: every value it reads, writes or returns has its declared type. Otherwise it refuses it, naming a location and a reason. The first stage, the <b>gate</b>, reads the TypeScript source and refuses what lies outside the language TScert admits; the <b>type reader</b> reads annotations and library declarations; the <b>producer</b> proposes a type for each expression; the later stages search for a proof of those types and check it."),
      card("Contract", "TScert's reviewed description of code it does not check itself: a function of JavaScript's standard library, of Node, or of TypeScript's compiler interface, each listed with its exact declaration and audited by hand. A contract is an assumption the result rests on: adding one widens what TScert trusts. A library global with no contract is refused; a function imported from a library with no contract is read through its declaration's written types."),
      card("Case, gap case", "A <b>case</b> is a small TypeScript file with the outcome TScert must give it, checked by the test suite (make suite). A <b>gap case</b> is one TScert refuses for want of a rule or a contract, though the program is safe: it turns into a verified case once the missing piece is added."),
    ]),
  }),
  slide("find", {
    label: "Part 1 · where proofs fail", title: "Two censuses of main, at c62a911 and acd7436 (2026-10-29)", gap: 22,
    body: cards([
      stat("303 of 602", `functions of tools/ ${status("ok", "verified")} by the census at c62a911, 2,431 of 14,625 statements (16.6%, measured); 281 of 586 at 1c35793, beside the diagnostic census at 4d25222 the last version of this deck used`, "ok"),
      stat("504 of 561", "copies the diagnostic census at acd7436 takes to their end (below); 46 stop at the 300 s limit of a stage, 11 of them before any refusal is reported; 11 at regions it cannot examine (measured)"),
      stat("33.0%", "coverage with holes: 4,822 of 14,625 statements outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a copy, also called a slice) and run through TScert (make census). A refused function stops at its first reason. A copy may hold several functions."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified. It ran at acd7436, one commit after c62a911, which changes no file of tools/."),
      point("Causes", "every refusal naming one construct counts, at whatever stage. Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number. A function whose diagnostic run reports only reasons naming no construct (a failed search), or none before the limit, counts under its first refusal in the census at c62a911: the source at the place that refusal names is read for the construct there (a judgement)."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example, where one is found", gap: 20,
    body: code(["// a five-line source that the census site at fragment-expressions.mts l.1939 reduces to",
      "type E = { readonly k: \"id\"; readonly name: string }",
      "  | { readonly k: \"optional\"; readonly receiver: E; readonly at: number };",
      "export function receiverOf(chain: E & { k: \"optional\" }): E {",
      "  return chain.receiver;   // refused: missing field receiver", "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from a census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("This census", "seven of the ten heaviest causes, numbered on the next slide, have no case. The source above, not yet a case of the suite, reproduces cause 5 (measured). For causes 1 and 2 no small source is found yet: the same shape over the program's own types verifies (cause 1, measured), and a source over compiler nodes needs the compiler interface's contract, which a scratch project does not load. Writing these cases is the next step."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at acd7436", title: "The ten causes that block the most code", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [5, 51, 11, 10, 23]) + bullets([
      "A function blocked by several causes counts under each; statements and functions are measured. Cause 6, and 26 of cause 3's 28 functions, are in code the commit e499515 added since the last version (slide “Code added since the last version”).",
      point("Judgements", "causes 1, 2, 5, 7, 8 and 9, and 29 of cause 4's 30 functions, count by the first refusal at c62a911 (slide “Two censuses”, Causes); collectDeclarations and lowerFile reach the limit before any refusal."),
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · cases by priority, continued", title: "Causes 11–18, by statements", gap: 16,
    body: table(["Cause", "Statements", "Functions", "Cases"], more, [52, 12, 10, 26]) + bullets([
      point("Refusals naming no construct", "99 functions, 2,187 statements, meet no cause (measured), the largest collect (394) and selectGlobal (346); in selectGlobal, only.binders is a read the producer and TypeScript type differently."),
      point("Further causes meeting at least 10 functions", "none beyond these; 298 refused functions, 12,180 statements, in all (measured)."),
    ]),
  }),
  slide("moved", {
    label: "Part 2 · since the last version", title: "The ten causes of the last version: nine closed, one narrowed", gap: 16,
    body: table(["Cause at 4d25222, the last version", "At 4d25222", "Status, by"], lastVersion, [46, 14, 40]) + bullets([
      "Statements · functions, measured at 4d25222; what is left, at acd7436. collectDeclarations now passes the gate, and its first refusal is cause 1 of slide “The ten causes”. The routes (support, a repair, avoidance) are defined on slide “Eight routes”.",
    ]),
  }),
  slide("moved-round", {
    label: "Part 2 · since the last version, further down", title: "Nine more causes of the last version: five closed, four narrowed", gap: 16,
    body: table(["Cause at 4d25222", "At 4d25222", "At acd7436", "Status, by"], further, [42, 12, 12, 34]) + bullets([
      "Statements · functions, measured; at acd7436 a function whose diagnostic run names no construct counts by its first refusal at c62a911, which the count at 4d25222 did not do. Routes: slide “Eight routes”.",
      "The object-pattern row's one function, selectGlobal, stays refused at another site, only.binders (slide “Causes 11–18”).",
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”, which also records each repair, avoidance and host boundary. Of the last version's ten causes, all ten took route 1, two of them by a contract."]),
  }),
  cause("omit", "Closed by 916de07 · 3,051 statements, 4 functions at 4d25222", "Closed: Omit of an interface", {
    cases: "", source: ["// blocker-omit-interface: verified", "interface Entry { stated: number; name: string; readonly kind: \"a\" | \"b\"; note?: string; }",
      "export function rest(e: Entry): Omit<Entry, \"stated\"> {", "  return { name: e.name, kind: e.kind };", "}"],
    why: "the library declares Omit&lt;T, K&gt; as Pick&lt;T, Exclude&lt;keyof T, K&gt;&gt;, and keyof over a type parameter has no term in TScert's type reader: it names a set of keys only once T is known. collectDeclarations, selectGlobal and two functions of library-modules.mts wrote Omit of their own interfaces.",
    todo: "",
    trust: "nothing: TypeScript computes the kept keys, and the type reader reads each kept member with its modifiers (readonly, optional).",
    closed: { status: `${verifies("blocker-omit-interface")}; ${neg("invalid-omit-omitted-member", "invalid-omit-readonly")}`,
      how: "route 1, support: Omit of an interface or an object alias is read as Pick at the keys TypeScript computes for Exclude&lt;keyof T, K&gt;. Omit of a class, a union, a type parameter, an index signature or a unique symbol stays refused, each a gap case.",
    },
  }),
  slide("collect-declarations", {
    label: "Causes 2–7 of the last version · 2,704 statements, 1 function", title: "collectDeclarations: six gate refusals closed", gap: 18,
    note: `${status("ok", "closed")} all six; ${verifies("blocker-returntype-typeof", "compiler-api-symbol-tables", "optional-method-call-object", "declaration-list-patterns")}`,
    body: table(["Construct", "Closed by"], [
      ["A callback parameter TypeScript types at a type parameter not in scope", "99224c2: a closure at a generic signature takes its type parameters"],
      ["The compiler enum TypePredicateKind", `cdbef56: a contract entry, ${trust}`],
      ["An optional call of a method whose object is a call, f(x).m?.(y)", "ba56fa4: the call saves its object, then tests the method"],
      ["A declaration list of two destructuring patterns", "faeefe4: lowered declarator by declarator"],
      ["ReturnType of a local function's typeof", "3911301: the result of the function's last signature"],
      ["Symbol's getExports and getMembers", `cdbef56: contract entries, ${trust}`],
    ], [52, 48]) + bullets([
      "collectDeclarations reads the declarations of a library: 2,774 census statements at acd7436. Each closure is route 1; cdbef56 adds a repair (route 3), a predicate's kind tested before its index. It passes the gate now, and its first refusal is at a read of node.moduleSpecifier (cause 1 of the table). Its diagnostic run reaches the 300 s limit in the producer before reporting any refusal, so what lies past the first refusal is not examined (measured).",
      point("What cdbef56 trusts", "TypePredicateKind's runtime object holds its declared values; getMembers and getExports return the symbol's own table, a Map keyed by the compiler's escaped names; code outside the program writes only such Maps into a symbol's tables."),
    ]),
  }),
  cause("optional-discriminant", "Closed by ba56fa4 · 1,168 statements, 9 functions at 4d25222", "Closed: a union's arm read after a test through an optional chain", {
    cases: "", source: ["// optional-chain-discriminant: verified (also run under Node)",
      "type Answered<T> = { readonly ok: true; readonly value: T } | { readonly ok: false; readonly refused: string };",
      "export function pick(m: Map<string, Answered<number>>, k: string): number | null {",
      "  const found = m.get(k);", "  return found?.ok ? found.value : null;", "}"],
    why: "found?.ok is true only where found is present and is the arm where ok is true, yet after it the producer reported found.value a missing member: the test did not narrow found to that arm. lowerFile (714 statements) met it at two sites, classBody (350) at one.",
    todo: "",
    trust: "nothing: the rule follows from the meaning of ?. and of the plain test.",
    closed: { status: verifies("optional-chain-discriminant"),
      how: "route 1, support: an optional chain of named reads on a name, read only for its truthiness (a condition, an operand of !, &&, ||), is truthy only where its receiver is present and the field is truthy, so it narrows the receiver as the plain test would. lowerFile and classBody now stop at causes 2 and 8 of the table.",
    },
  }),
  cause("local-function", "Closed by e499515 · 305 statements, 2 functions at 4d25222", "Closed: a function declaration inside a function", {
    cases: "", source: ["// function-declarations-in-body: verified (also run under Node)", "export function hoisted(): number {", "  const r = twice(2);",
      "  function twice(n: number): number { return n * 2; }", "  return r;", "}"],
    why: "JavaScript creates a declared function when its block is entered, so a call above the declaration works; one that runs before a let or const it reads is initialized throws. The gate refused every function declaration in a body: familyTable's combine and deepPartMap's three.",
    todo: "",
    trust: `${trust}: the gate's placement of a declaration: no mention of it, outside types and property keys, runs before the statement it is placed at. The placement is computed by the gate, unproved.`,
    closed: { status: `${verifies("function-declarations-in-body", "dead-code-hoisted")}`,
      how: "route 1, support: the declaration is a constant holding its closure, bound before the first statement that may mention it; a let or const it reads that is declared later is checked at each read. The code computing the placement is itself refused, causes 3 and 6 of the table (next slide).",
    },
  }),
  slide("added-code", {
    label: "Cause 6 · 686 statements, 25 functions; cause 3 · 721 of its 818, 26 of its 28", title: "Code added since the last version, refused by TScert", gap: 18,
    note: `cause 3 ${gap("for-let-capture-refused")}; cause 6 ${noCase}`,
    body: code(["// fragment-statements.mts, functionPlacement (l.659), from e499515",
      "for (let changed = true; changed;) {", "  changed = false;", "  live.forEach((s, i) => { … placed.set(f, at); changed = true; … });", "}",
      "// fragment-statements.mts, markEarly (l.807): visit, a closure declared above, reads statementStart",
      "let statementStart = -1;"]) + bullets([
      point("Why they are refused", "JavaScript gives each iteration of a for loop its own copy of the loop's let, and TScert binds it once, so a closure capturing it is refused (cause 3). A let a closure may read before its declaration has run must state its type (cause 6). Both are met by every copy of fragment-statements.mts that reaches these two functions."),
      point("What closing needs", "a repair of each site, route 3 (a judgement): the loop over a let declared outside it, and the annotation let statementStart: number. Neither changes what the code computes. Cause 3's two older sites, in guardClosure and freeOffsets (97 · 2), stay."),
      point("What it would trust", "nothing."),
    ]),
  }),
  cause("let-guard-narrowing", "Cause 1 · 2,798 statements, 2 functions", "A member read on a let narrowed by two compiler guards", {
    cases: "", note: `${noCase}: the same shape over the program's own types verifies (measured)`,
    source: ["// declaration-graph.mts l.317–322 (collectDeclarations, statementsOnPath)", "let node: Node | undefined = symbol.declarations[0]?.resolve();",
      "while (node && !ts.isImportDeclaration(node) && !ts.isExportDeclaration(node) && !ts.isSourceFile(node))", "  node = node.parent;",
      "if (node && (ts.isImportDeclaration(node) || ts.isExportDeclaration(node))) {", "  out.push(node);", "  if (node.moduleSpecifier) starExports(node.moduleSpecifier);   // refused: missing field moduleSpecifier", "}"],
    why: "after the test, node is an import or an export declaration, both of which declare moduleSpecifier, yet the producer reports it a missing member (measured in the census at c62a911). A source of the same shape over three record types and two guards of the program verifies, so the cause lies with the compiler's guards or node types; which one is not established.",
    todo: "first a case example that reproduces the refusal over the compiler's types; then the rule or the contract entry it shows missing.",
    trust: "not known until the cause is established.",
  }),
  cause("node-callback-signature", "Cause 2 · 1,069 statements, 10 functions", "A callback over compiler nodes, claimed outside its annotation", {
    cases: "", note: `${noCase}`,
    source: ["// fragment-parse.mts l.2208 (lowerFile and 6 functions calling it)", "const node = [...importNodes, ...localNodes, ...globalNodes].find(n =>",
      "  n.getStart(source) === root.binding.span[0]) ?? first;", "// type-probe.mts (makeProbe): copied.find(n => n.getSourceFile().fileName === …)"],
    why: "the arrow n => … has no annotation, so its type is the one find's declared callback parameter gives it; the search rejects the type the producer claims for the arrow as lying outside that one (“closure signature claim is outside the source annotation”, the first refusal at c62a911). The ten functions meet four sites, each a callback over an array of compiler nodes: the one above, shared by lowerFile and its six callers, makeProbe's and globalFunction's find, importBindings' flatMap. What makes the claim differ is not established.",
    todo: "a case example over compiler nodes, then the rule or repair it shows missing.",
    trust: "not known until the cause is established.",
  }),
  cause("recursive-union-join", "Cause 4 · 780 statements, 30 functions", "Grouped switch cases returning at one site", {
    cases: "blocker-recursive-union-join",
    source: ["// type-term.mts, restRefusal (l.196); reached by 30 copies of type-term.mts", "switch (type.k) {", "  case \"parameter\": return `${REST_CONTRACT}: …`;   // … one case per kind",
      "  case \"array\": case \"union\": case \"reference\":", "    return REST_CONTRACT;   // refused: the incoming edge does not establish its claims", "  default: return `${REST_CONTRACT}: …`;", "}"],
    why: "type is a TypeTerm, a recursive union of records discriminated by k. Three case labels reach one return, and the search finds no proof that the claims at that return hold on every edge into it (measured; the case reproduces it). It is the first refusal of 30 of the 34 refused copies of type-term.mts in the census at c62a911.",
    todo: "join the knowledge of grouped case labels on a recursive union (route 1, a rule); or a repair at the one site, one return per label.",
    trust: "nothing.",
  }),
  cause("intersection-discriminant", "Cause 5 · 764 statements, 11 functions", "A union intersected with one arm's discriminant", {
    cases: "", note: `${noCase}: reproduced by the five-line source of Part 1 (measured)`,
    source: ["// fragment-expressions.mts l.1936–1939, chainReads", "function chainReads(gate: Gate, at: Node, chain: Expr & { k: \"optional\" }): … {", "  …",
      "  const receiver = chain.receiver;   // refused: missing field receiver"],
    why: "Expr is a union of records discriminated by k; Expr &amp; { k: \"optional\" } is exactly its optional arm, which declares receiver. The producer does not select that arm from the intersection and reports receiver a missing member. It is the first refusal at c62a911 of the copies of fragment-expressions.mts that reach chainReads (a judgement, slide “Two censuses”): expr (300 statements), binary (142), lambda (127) among the 11.",
    todo: "read the intersection of a discriminated union with one arm's discriminant as that arm (route 1, a rule); or a repair at the one site, the parameter typed by the arm's own name.",
    trust: "nothing: the intersection and the arm hold the same values.",
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What comes next: cases first, then rules and repairs", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. Case examples for causes 1, 2 and 5–9, each from its census site", "the source of Part 1 for cause 5; six to write", status("gap", "none")],
      ["2. Repairs of the code added since the last version (cause 6, and 26 of cause 3's functions)", c("for-let-capture-refused"), status("ok", "none")],
      ["3. Rules or repairs: grouped case labels (4), the discriminant intersection (5), the in test (7), the let's expected type (8)", c("blocker-recursive-union-join"), status("ok", "none expected")],
      ["4. Causes 1 and 2, once their cases show the cause", "", status("gap", "not known")],
      ["5. The decoders' closing assertions (9): the decoders take parsed JSON, read through a contract of JSON.parse", "", status("trust", "that contract")],
    ], [52, 30, 18]) + bullets([
      "The order follows the census process: first the case examples, then the repair in place of the code added since the last version, then the gap cases in the order of the code they block.",
      "The census and the diagnostic census, run once on main after these merges, measure what each gained.",
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert's proofs fail",
  slides,
  sections: [
    { description: "Where proofs fail, from the diagnostic census, and the case examples made.", start: "cover" },
    { description: "The cases by priority: open ones, what closing needs; closed ones, how and why.", start: "priority" },
  ],
};
export default deck;
