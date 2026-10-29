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
  ["1", "Omit&lt;I, K&gt; of an interface: keyof over a type parameter", "3,051", "4", gap("blocker-omit-interface")],
  ["2–7", "Six more gate refusals met only in collectDeclarations (slide “collectDeclarations”)", "2,704 each", "1", "one negative and one gap among them; four no case"],
  ["8", "A union's arm read after a test through an optional chain, x?.ok ? x.value : …", "1,168", "9", noCase],
  ["9", "A spread of a compiler node list or an empty array, ...(xs ?? [])", "781", "7", noCase],
  ["10", "A map callback returning a record literal of a discriminated union", "780", "31", gap("blocker-callback-literal-context")],
];

const more: [string, string, string, string][] = [
  ["A numeric key not proved an array index", "490", "5", gap("blocker-array-index-of-write")],
  ["An array pattern over a value with no array contract", "431", "3", "cases in cases.mts"],
  ["An assignment to a module's let, or its increment", "378", "42", gap("blocker-module-assignment")],
  ["A member read from Number.prototype after an earlier refusal (a judgement)", "340", "1", noCase],
  ["An object pattern's key spelled as a later local's name", "340", "1", gap("blocker-pattern-key-early-binding")],
  ["A test of an optional never field as a union's discriminant", "320", "1", gap("blocker-optional-never-discriminant")],
  ["A function declaration inside a function", "305", "2", gap("function-declaration-in-body-refused")],
  ["A field holding an object or null, reread after a test", "299", "8", gap("guard-field-assertion")],
];

const lastVersion: [string, string, string][] = [
  ["A member of a node read after isTypeAliasDeclaration", "2,052 · 37", closedBy("0fc7839, 8ec35f5", "a repair and a stated contract")],
  ["An optional chain reported as an unbound name ?.", "1,779 · 12", `${status("ok", "dropped")} df521bc: an artifact of diagnostic runs alone`],
  ["Number both called and read through its members", "1,113 · 24", closedBy("1da3887, c105173", "a rule")],
  ["A callback parameter whose context is a library type", "1,082 · 16", closedBy("25493e6", "a rule; a new site, runChild (38 · 1)")],
  ["Map and Set with no binding in the slice, or instanceof of them", "1,059 · 9", closedBy("467af18, dfbefbd", "a repair and a rule")],
  ["An array's method read where its type joins a record", "1,024 · 15", closedBy("83afafc, 6be11ce", "contract entries and a rule")],
  ["A member read after k in x, on an object of unknown type", "1,016 · 24", closedBy("e276727", "a rule")],
  ["A generic function used where its type parameters must be checked", "1,005 · 20", narrowedBy("82baee4", "a rule; left only in runChild (38 · 1)")],
  ["Array&lt;T&gt;: Array's library declaration refused", "887 · 10", closedBy("2df5f8d", "a rule")],
  ["Object.entries, whose overloads are generic and plain", "860 · 28", narrowedBy("317ff8f", "a rule; 80 · 3 left")],
];

const thisRound: [string, string, string, string][] = [
  ["1. A numeric key not proved an array index", "823 · 9", "490 · 5", narrowedBy("325f99c", "avoidance")],
  ["2. x instanceof C on a caught error typed unknown", "823 · 9", "none", closedBy("a802c04", "a repair")],
  ["3. An effect (what a function may change) stated on an overload", "804 · 8", "none", closedBy("aa84da6", "avoidance")],
  ["4. A constructor assignment reading this (class Gate)", "769 · 7", "none", closedBy("5d192c2", "avoidance")],
  ["5. A spread of an iterable in a conditional's branch", "757 · 30", "none", closedBy("747fd39", "avoidance")],
  ["6. A compiler Type method not reviewed (isUnionType …)", "667 · 17", "none", closedBy("6013121", "support")],
  ["7. A write adding a key to an object others hold", "630 · 25", "139 · 12", narrowedBy("f2d07f1", "a rule")],
  ["8. JSON.stringify with a replacer function", "489 · 4", "none", closedBy("0108092", "a repair")],
  ["9. Node's declarations reach ArrayBufferLike", "473 · 20", "none", `${status("ok", "gone")} with 10 (a judgement)`],
  ["10. node:url's functions and the global URL", "456 · 19", "none", closedBy("07c082b", "contracts and host boundaries")],
];

const modelled: [string, string][] = [
  ["A node list filtered by a compiler guard (387 · 2)", "035fe74: a guard passed by name to filter or find narrows the result"],
  ["Signature.declaration (351 · 2); checker queries at an array (197 · 4)", "a8cba50: compiler-API contract entries"],
  ["import.meta (319 · 28)", "6338776: its members are unknown values stating no effect"],
  ["new Set of a Set, new Map of a Map (193 · 7)", "c797d9a: a copy through the built-in iterator"],
  ["A default import of node:path, node:fs (187 · 3, 106 · 2)", "d59d4cc: each member is the module's named export"],
  ["A replacement callback with captures (167 · 3)", "a1e3657: each capture is a string or undefined"],
  ["Reflect (221 · 6), Object.getPrototypeOf (111 · 5)", "8987151: Reflect.ownKeys, a comparison with Object.prototype; 4 · 2, 31 · 2 left"],
  ["node:module's hooks (69 · 5)", "1c35793: a host boundary, module-hooks.mts; its 4 functions stay refused"],
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
    label: "Part 1 · where proofs fail", title: "Two censuses of main, at 1c35793 and 4d25222 (2026-10-29)", gap: 22,
    body: cards([
      stat("281 of 586", `functions of tools/ ${status("ok", "verified")} by the census at 1c35793, 2,265 of 14,220 statements (15.9%, measured); 227 of 519 at b81675f, the census the last version of this deck used`, "ok"),
      stat("488 of 549", "copies the diagnostic census at 4d25222 takes to their end (below); 42 stop at the 300 s limit of a stage, 18 at regions it cannot examine, 1 at a failure of a stage (measured)"),
      stat("30.9%", "coverage with holes: 4,403 of 14,228 statements outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a copy, also called a slice) and run through TScert (make census). A refused function stops at its first reason. A copy may hold several functions."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified. It ran at 4d25222, two commits after 1c35793."),
      point("Causes", "every refusal naming one construct counts, at whatever stage. Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number. A refused read whose own object an inner read already failed on (x.a.b after x.a) counts under the inner one."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example, where one is found", gap: 20,
    body: code(["// a five-line source that the census site at fragment-parse.mts l.605 reduces to",
      "type Answered<T> = { readonly ok: true; readonly value: T } | { readonly ok: false; readonly refused: string };",
      "export function pick(m: Map<string, Answered<number>>, k: string): number | null {",
      "  const found = m.get(k);", "  return found?.ok ? found.value : null;   // refused: missing field value", "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from a census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("This census", "six of the ten heaviest causes have no case: causes 8 and 9, whose refusals the source above and a 3-line spread of a node list reproduce (measured), and four of the gate refusals of collectDeclarations (slide “collectDeclarations”). Writing their cases is the next step."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at 4d25222", title: "The ten causes that block the most code", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [5, 49, 12, 10, 24]) + bullets([
      "A function blocked by several causes counts under each. Statements and functions are measured. Causes 1–7 are all met in collectDeclarations (2,704 statements), the largest function of tools/: all seven must be closed before it can verify, and what its run meets after the gate is not examined.",
      point("Judgements", "causes 8–10 are sites read in the source, each behind a reason that names no construct (a missing member, a failed search); cause 10 counts the 31 copies of type-term.mts that reach emptyObject, where the verified census stops 29 of them."),
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · cases by priority, continued", title: "Causes 11–18, by statements", gap: 16,
    body: table(["Cause", "Statements", "Functions", "Cases"], more, [54, 12, 10, 24]) + bullets([
      point("Refusals naming no construct", "a failed search or a missing member counts under the construct refusal its function meets (a judgement); 90 functions, 2,031 statements, meet none (measured), the largest collect (387)."),
      point("Further causes meeting at least 10 functions", "an imported class's type parameter default (245 · 13), JSON.stringify of a record (213 · 16, refused rightly), a key-adding write (139 · 12), a record field's function passed to map (138 · 14)."),
    ]),
  }),
  slide("moved", {
    label: "Part 2 · since the last version", title: "The ten causes of the last version: seven closed, one dropped, two narrowed", gap: 16,
    body: table(["Cause at b81675f, the last version", "At b81675f", "Status, by"], lastVersion, [46, 14, 40]) + bullets([
      "Statements · functions, measured at b81675f; what is left, at 4d25222. The commits lie between b81675f and 6be11ce.",
    ]),
  }),
  slide("moved-round", {
    label: "Part 2 · this round", title: "The ten heaviest causes at 6be11ce: seven closed, two narrowed, one gone", gap: 16,
    body: table(["Cause at 6be11ce", "At 6be11ce", "At 4d25222", "Status, by"], thisRound, [42, 12, 12, 34]) + bullets([
      "The diagnostic census of 6be11ce ranked these causes; no version of this deck showed it. Measured in both by the same counting.",
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”, which also records each repair, avoidance and host boundary. Of this round's ten causes, two took route 3, four route 4 (the familyTable site of 1 among them), and three route 1, one of them with route 5."]),
  }),
  cause("instanceof-unknown", "Closed by a802c04 · 823 statements, 9 functions at 6be11ce", "Closed: the fields of a caught error, read after instanceof", {
    cases: "", source: ["// instanceof-unknown-refused: refused, rightly (the suite files it as a gap)", "class Point { x: number = 0; }", "export function px(p: unknown): number {",
      "  if (p instanceof Point) return p.x;", "  return 0;", "}"],
    why: "a catch binds unknown, and x instanceof C holds of any object with C's prototype on its chain, whether C's constructor made it or not (Object.create(C.prototype)), so the test establishes no field. TScert's handlers read error.pos, error.message and error.at after such a test: lowerFile, recoverGate and diagnosticFragment among the 9.",
    todo: "",
    trust: `${trust}: WeakMap's constructor and its get, has, set and delete are a contract.`,
    closed: {
      status: `${status("ok", "verified")} native-weakmap, blocker-weakmap; ${neg("instanceof-unknown-refused")}`,
      how: "route 3, a repair: the code had the fields where it threw and lost them at the catch. Each maker records an error's fields in a WeakMap keyed by the error object, and a handler finds them there. The case's refusal is right, though the suite keeps it as a gap; no site of TScert's code reaches it.",
    },
  }),
  cause("within-overload", "Closed by aa84da6 · 804 statements, 8 functions at 6be11ce", "Closed: an effect stated on an overloaded declaration", {
    cases: "", source: ["// invalid-stated-overload-value-import: refused, rightly", `import { pick } from "@fixture/stated-overload";`,
      "export function picked(xs: number[]): number {", "  return pick(xs, true);", "}"],
    why: "TScert certifies a function's body at one signature, its implementation's, so it has no check for an effect statement (a result type Within&lt;F, T&gt;: the result T, with F what the function may change) on an overload or on an implementation beside overloads, and refuses it wherever the declaration is read, rightly: no body is checked against it. resolutionSlots in type-term.mts stated its effect beside two overloads; lowerFile (703 statements) and intrinsics read it.",
    todo: "",
    trust: "nothing: no rule and no contract changes.",
    closed: { status: `${status("ok", "closed")}; ${neg("invalid-stated-overload-value-import", "invalid-stated-one-overload-value-import")}`,
      how: "route 4, avoidance: resolutionSlots states its effect at one signature, and a second function, resolvableSlots, states the result the other overload gave. Each call returns what it returned before.",
    },
  }),
  cause("gate-class", "Closed by 5d192c2 · 769 statements, 7 functions at 6be11ce", "Closed: a constructor assignment reading this", {
    cases: "", source: ["// blocker-constructor-assignment-this: a gap, kept", "export class Counter {", "  readonly start: number; readonly next: number;",
      "  constructor(start: number) { this.start = start; this.next = this.after(); }", "  after(): number { return this.start + 1; }", "}"],
    why: "the gate refuses a constructor statement that reads this: TScert allocates the instance at the constructor's end from one value per field, so no instance exists while the constructor runs. TScert's class Gate assigned its field scope from this.termScope(), a call whose closures read the other fields.",
    todo: "",
    trust: "nothing: no rule and no contract changes.",
    closed: { status: `${status("ok", "closed")}; ${gap("blocker-constructor-assignment-this")}`,
      how: "route 4, avoidance: the gate's term scope is computed where it is read. Admitting the call would allocate the instance before it and add the remaining fields after it, to an object the call's closures already reference, which no rule covers; this was the construct's one site.",
    },
  }),
  cause("iterable-spread-gate", "Closed by 747fd39 · 757 statements, 30 functions at 6be11ce", "Closed: a spread of a program's iterable in a conditional's branch", {
    cases: "", source: ["// blocker-spread-in-conditional: a gap, kept", "export function names(term: Term, bound: ReadonlySet<string>): ReadonlySet<string> {",
      `  return term.k !== "scheme" ? bound : new Set([...bound, ...term.binders]);`, "}"],
    why: "a ReadonlySet is an interface any object may implement, so its iterator may run the program's code. TScert steps such an iterator before the statement holding the spread; JavaScript steps it after the test, and only in the branch the test selects. visitType in type-term.mts, reached by 30 copies, was the census's one site.",
    todo: "",
    trust: "nothing: no rule and no contract changes.",
    closed: { status: `${status("ok", "closed")}; ${gap("blocker-spread-in-conditional")}`,
      how: "route 4, avoidance: visitType builds a scheme's scope in an if, so the spread runs first in its statement. 28 of the 30 copies then stop at cause 10 of the priority table, the map callback (slide “callback-literal-context”; measured in the census at 1c35793).",
    },
  }),
  cause("compiler-type", "Closed by 6013121 · 667 statements, 17 functions at 6be11ce", "Closed: the compiler's type predicates, read with their promise", {
    cases: "", source: ["// invalid-compiler-api-sync-guard: refused, rightly", `import { isIntrinsicType, type Type } from "typescript/unstable/sync";`,
      "export function name(type: Type): string | undefined {", "  return isIntrinsicType(type) ? type.intrinsicName : undefined;", "}"],
    why: "TScert's readers of compiler types wrote type.isUnionType() ? type.getTypes() : [type]. A predicate's promise is the type it guarantees where it answers true (x is X). The compiler-API contract read every predicate without its promise, so the test narrowed nothing and getTypes was no member of Type; the method isUnionType was no listed member of Type at all. makeProbe and indexedAccess were the heaviest of the 17.",
    todo: "",
    trust: `${trust}: on a compiler object a stated guard answers true for, the members its promise names exist (the contract's assumption T7).`,
    closed: { status: `${status("ok", "verified")} compiler-api-stated-guards; ${neg("invalid-compiler-api-sync-guard", "invalid-compiler-api-type-method")}`,
      how: "route 1, support: the predicates the code uses are stated guards; route 4 at the method form, rewritten as the guard function (its promise is about the receiver, which no rule narrows). A predicate with no stated promise stays read without one (the case).",
    },
  }),
  cause("json-replacer", "Closed by 0108092 · 489 statements, 4 functions at 6be11ce", "Closed: JSON.stringify with a replacer function", {
    cases: "", source: ["// invalid-json-stringify-replacer: refused, rightly", "export function wrong(xs: number[], replacer: (key: string, value: unknown) => unknown): number[] {",
      "  return xs.map((x) => { JSON.stringify(x, replacer); return x; });", "}"],
    why: "a replacer is the program's code that JSON.stringify calls on every member, with the holder as this, and what it returns is serialized in turn, so it may change the array map visits. TScert's code keyed type terms by JSON.stringify(t, (key, v) => key === \"span\" ? undefined : v) in collect (387 statements) and named-record.mts.",
    todo: "",
    trust: "nothing: the refusal stays, and the code changes.",
    closed: { status: `${status("ok", "verified")} typed-tree-text; ${neg("invalid-json-stringify-replacer")}`,
      how: "route 3, a repair: a type term's text is written kind by kind from its type, without a replacer. collect then stops at other refusals (among the functions no cause is established for, slide “Causes 11–18”).",
    },
  }),
  cause("node-url", "Closed by 07c082b · 456 statements, 19 functions at 6be11ce", "Closed: node:url's functions and the global URL", {
    cases: "", source: ["// blocker-node-url-import: verified", `import { fileURLToPath } from "node:url";`, `import { resolveHref, pathToFileHref } from "../../tools/url-strings.mts";`,
      "export function target(specifier: string, parent: string): string | null {",
      "  try { return fileURLToPath(resolveHref(specifier, pathToFileHref(parent))); } catch { return null; }", "}"],
    why: "Node's declarations of node:url reach URLSearchParams and iterator types the type reader refuses, so fileURLToPath, pathToFileURL and new URL were refused in family-activation.mts, files.mts and unchecked.mts.",
    todo: "",
    trust: `${trust}: new URL of strings, fileURLToPath of a string and pathToFileURL are overlay contracts; two host boundaries, tools/url-strings.mts and tools/child-output.mts, give their values the stated types.`,
    closed: { status: `${status("ok", "verified")} blocker-node-url-import`,
      how: "route 1, support, for the three functions; route 5 for the rest: the program holds URLs only as strings, made and resolved in url-strings.mts, and a child process's output is read in child-output.mts. ArrayBufferLike (9 of the table) is met in no function since (a judgement: 19 of its 20 functions met node:url).",
    },
  }),
  cause("key-adding-write", "Narrowed by f2d07f1 · 630 statements, 25 functions at 6be11ce", "Narrowed: a key-adding write in a loop", {
    cases: "", source: ["// blocker-loop-key-adding-write: verified", "export function lengths(names: readonly string[]): { [key: string]: number } {",
      "  const metadata: { [key: string]: number } = {};", "  for (const key of names) metadata[key] = key.length;", "  return metadata;", "}"],
    why: "a write at a key an object may not hold adds the key, and another reference to the object, typed before the write, would not see it in its type. In a loop TScert could not show that no other reference exists.",
    todo: "",
    trust: `${trust}: that no other reference escapes is a syntactic analysis, unproved; the copy itself is checked. Four negative cases.`,
    closed: { narrowed: true, status: `${status("ok", "verified")} blocker-loop-key-adding-write; 4 negative cases`,
      how: "route 1, a rule: in a loop, a write that adds a key is read as building a copy of the object, where no statement of the loop lets another reference to it escape. Open, 12 functions and 139 statements: writes to an object a parameter or another binding holds (copied, openCompiler, guardClientRequests …).",
    },
  }),
  slide("modelled", {
    label: "Part 2 · this round, external code described", title: "Causes closed by a contract or a host boundary", gap: 16,
    body: table(["Cause at 6be11ce (statements · functions)", "Closed by (route 1, or 5 for a boundary)"], modelled, [44, 56]) + bullets([
      `Each but 8987151 adds a contract or a boundary, a ${trust} its commit states; each has a verified case. What is left is measured at 4d25222.`,
      "The narrowed numeric key (1 of the table of 6be11ce): 325f99c rewrites familyTable without a write at the index indexOf finds (route 4).",
    ]),
  }),
  slide("collect-declarations", {
    label: "Causes 1–7 · 2,704 statements, 1 function, and Omit in 3 more", title: "collectDeclarations: seven gate refusals", gap: 18,
    note: `${gap("blocker-omit-interface", "optional-method-call-object-refused")}; ${neg("invalid-compiler-api-unlisted-enum")}; four ${noCase}`,
    body: table(["Construct", "Site"], [
      ["Omit of an interface, keyof over a type parameter (also selectGlobal and library-modules.mts)", "l.1784 Omit&lt;…&gt;"],
      ["A method of the compiler's Symbol not reviewed: getExports, getMembers", "l.4038–4042"],
      ["A compiler enum the contract does not read: TypePredicateKind", "l.8, the import"],
      ["ReturnType of a local function's type", "l.4031 ReturnType&lt;typeof targetOf&gt;"],
      ["An optional call of a method whose object is a call", "l.2075 valueScope(…).equation?.(reference)"],
      ["A callback parameter TypeScript types at a type parameter not in scope", "l.2657, the parameter read"],
      ["A declaration list of two destructuring patterns", "l.3282 const [member] = members, [owner] = owners"],
    ], [58, 42]) + bullets([
      "collectDeclarations reads the declarations of a library: 2,704 census statements. Its diagnostic run stops after the gate at the 300 s limit, so what lies after these seven is not examined (measured).",
      point("What closing needs", "for the enum and Symbol's methods, contract entries audited against the compiler (route 1, a trust change each); for the other five, a rule each or a rewrite (route 4). Several are one site, so a rewrite is the likely route (a judgement)."),
    ]),
  }),
  cause("optional-discriminant", "Cause 8 · 1,168 statements, 9 functions", "A union's arm read after a test through an optional chain", {
    cases: "", note: `${noCase}: reproduced by the five-line source of Part 1`,
    source: ["// fragment-parse.mts l.605 (lowerFile and 6 more), fragment-classes.mts l.547 (classBody, classStmt)",
      "const found = this.symbolNames.get(this.span(name.expression).join(\":\"));", "const symbol = found?.ok ? found.value : null;"],
    why: "found is Answered&lt;T&gt; | undefined, a union of { ok: true; value } and { ok: false; refused }. The test found?.ok is true only where found is the first arm, yet after it the producer reports found.value a missing member (measured): the test does not narrow found to that arm. lowerFile (714 statements) meets it at two sites, classBody (350) at one.",
    todo: "narrow a value by a discriminant test through an optional chain, as by the plain test after found !== undefined (route 1, a rule).",
    trust: "nothing: the rule follows from the semantics of ?. and of the plain test.",
  }),
  cause("nodelist-spread", "Cause 9 · 781 statements, 7 functions", "A spread of a compiler node list or an empty array", {
    cases: "", note: `${noCase}: reproduced by a 3-line source`,
    source: [`import * as ts from "typescript/unstable/ast";`, "export function keys(out: ts.TypeNode[], node: ts.TypeReferenceNode): void {",
      "  out.push(...(node.typeArguments ?? []));   // refused", "}"],
    why: "the operand is a node list (an array met with a record of its own members, pos and end among them) or an empty array literal. The producer spreads an array or a tuple of required positions, and refuses this union: “generic spread requires an array or a tuple of required positions”. The same spread of readonly string[] | undefined verifies (measured). In tools/, keyTypeNodes.push(…) in lowerFile.",
    todo: "spread a union whose every member has an array view by its element type (route 1, a rule); or a repair at the one site, a loop over the node list.",
    trust: "nothing: a node list's iteration is already its array view's.",
  }),
  cause("callback-literal-context", "Cause 10 · 780 statements, 31 functions", "A map callback returning a record literal of a discriminated union", {
    cases: "blocker-callback-literal-context",
    source: ["// type-term.mts, emptyObject", `function emptyObject(span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {`,
      `  return { k: "union", span, parts: (["boolean", "number", "string", …] as const)`, `    .map(name => ({ k: "atom", name, span })) };`, "}"],
    why: "the callback's result has no annotation, and the result emptyObject states, a TypeTerm (a union of records discriminated by k), is not carried into it, so the search finds no proof that the returned literal { k: \"atom\", name, span } is a TypeTerm. Every copy of type-term.mts that reaches emptyObject meets it; in 29 of them it is the first refusal once the spread of this round's cause 5 is avoided (measured in the census at 1c35793).",
    todo: "carry map's expected result type into the callback's returned literal, as an annotation of the callback's result would (route 1, a rule); or a repair at the one site, an annotated callback.",
    trust: "nothing.",
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What comes next: cases first, then rules and rewrites, then external code", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. Case examples for causes 8 and 9 and for collectDeclarations's four without one", "the sources of Part 1 and of cause 9; four to write", status("gap", "none")],
      ["2. Rules or rewrites: the optional-chain test (8), the node-list spread (9), map's expected result (10), collectDeclarations's five refusals that need no contract, Omit (1) among them", `${c("blocker-callback-literal-context")}, ${c("blocker-omit-interface")}, ${c("optional-method-call-object-refused")}`, `${status("ok", "none")}`],
      ["3. External code described: the compiler's Symbol methods and TypePredicateKind (collectDeclarations)", c("invalid-compiler-api-unlisted-enum"), status("trust", "an audited entry each")],
    ], [50, 34, 16]) + bullets([
      "The order follows the census process: sites where TScert's own code discards what it knew are repaired first (none among the heaviest causes); then the gap cases in the order of the code they block. collectDeclarations can verify only once causes 1–7 are all closed (beyond them its run is not examined), so it is worked as one case.",
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
