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
const noCase = status("gap", "no case");

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
  ["1", "A member of a node read after isTypeAliasDeclaration", "2,052", "37", gap("blocker-type-alias-guard-member")],
  ["2", "An optional chain the producer reports as an unbound name ?.", "1,779", "12", noCase],
  ["3", "Number both called and read through its members", "1,113", "24", gap("number-call-and-members")],
  ["4", "A callback parameter whose context is a library type", "1,082", "16", gap("blocker-closure-map-context")],
  ["5", "Map and Set: no binding in the slice, or instanceof of them", "1,059", "9", noCase],
  ["6", "An array's method read where its type joins a record", "1,024", "15", gap("blocker-array-finally-view")],
  ["7", "A member read after k in x, on an object of unknown type", "1,016", "24", gap("blocker-in-name-object")],
  ["8", "A generic function used where TScert cannot check its type parameters", "1,005", "20", noCase],
  ["9", "Array&lt;T&gt;: Array's library declaration refused", "887", "10", gap("blocker-array-generic-annotation")],
  ["10", "Object.entries, whose overloads are generic and plain", "860", "28", gap("blocker-entries-mixed-overloads")],
];

const more: [string, string, string, string][] = [
  ["A for statement's condition, not found after ts.isForStatement on a union of loops", "663", "22", noCase],
  ["A method of the compiler's Type TScert has not reviewed (isUnionType …)", "660", "17", `${status("neg", "refused until reviewed")} ${c("invalid-compiler-api-sync-guard")}`],
  ["A write that may add a key to an object others hold", "630", "25", gap("blocker-loop-key-adding-write")],
  ["ArrayBufferLike, reached through a global's declaration", "473", "20", noCase],
  ["node:url's functions: their declarations reach a type the type reader refuses", "456", "19", gap("blocker-node-url-import")],
  ["An assignment to a module's let, or its increment (each refused increment is of one)", "387", "42", gap("blocker-module-assignment")],
  ["An imported class whose type parameter has a default (API)", "245", "13", gap("blocker-compiler-api-value-default")],
  ["import.meta", "190", "25", gap("blocker-import-meta")],
];

const moved: [string, string, string, string][] = [
  ["An optional method read as a type, and bound (record hook)", "1,188 · 25", "none", `${status("ok", "closed")} c6e7119, a repair`],
  ["A dictionary read at a key that may name a member of Object.prototype", "1,112 · 27", "none", `${status("ok", "closed")} a03f12a, a repair`],
  ["A key test k in x on an operand typed unknown", "1,282 · 51", "none", `${status("ok", "narrowed")} d578dd8, a rule: the test is admitted, the read after it is cause 7`],
  ["A spread of a value that may not be a plain object", "695 · 17", "3 · 1", `${status("ok", "narrowed")} d578dd8, the same rule`],
  ["A numeric key not proved an array index", "1,470 · 17", "779 · 9", `${status("ok", "narrowed")} b276cd5, a rule`],
  ["A field holding an object, reread after a test of it", "828 · 17", "300 · 8", `${status("ok", "narrowed")} 05041cf, a rule`],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and most functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and turns each cause into a small case example. Part 2 ranks those cases by how much code they block, and shows for each case closed since the last version how and why it was closed, and for each of the heaviest open ones what closing it needs.",
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
    label: "Part 1 · where proofs fail", title: "Two censuses of main at b81675f (2026-10-28)", gap: 22,
    body: cards([
      stat("227 of 519", `functions of tools/ ${status("ok", "verified")} by the census, 1,728 of 13,562 statements (12.7%, measured); 204 of 510 at the census of a0ffcd7, whose tools/ is aa7c768's, the one the last version of this deck used`, "ok"),
      stat("436", "functions the diagnostic census takes to their end (below); 14 stop at regions it cannot examine, 68 at the 300 s limit of a stage, 1 at a failure of the compiler interface (measured)"),
      stat("27.8%", "coverage with holes: 3,774 statements outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a slice) and run through TScert (make census). A refused function stops at its first reason. The verified census ran at 8092044, whose tools/ is b81675f's."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified."),
      point("Causes", "every refusal naming one construct counts, at whatever stage. Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number. A refused read whose own object an inner read already failed on (x.a.b after x.a) counts under the inner one."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example, where one is found", gap: 20,
    body: code(["// blocker-node-url-import.ts. Census functions: family-activation.mts#activeGuards, …",
      `import { fileURLToPath } from "node:url";`,
      "export function pathOf(url: string): string {", "  return fileURLToPath(url);", "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from a census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("Which causes get one", "every cause among the ten heaviest or meeting at least 10 functions. Five such causes have none (marked no case). For four (causes 2 and 8, the for statement and ArrayBufferLike), the smallest forms of their census sites written so far verify, so what the census meets there depends on more of the function than the site (a judgement); for Map and Set (cause 5) none is written yet. No new case example comes from this census."),
      point("Closing a case", "a fix makes it verify, and the census copies of its functions then pass that refusal and stop at the next."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at b81675f", title: "The ten causes that block the most code", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [4, 46, 11, 10, 29]) + bullets([
      "A function blocked by several causes counts under each. Statements and functions are measured.",
      point("Judgements", "cause 1 includes one site read in the source (findBlockTypes: 7 functions, 758 statements); cause 7 is 15 sites read in the source, each a read after a key test on a value typed unknown; cause 5 counts the loops over Map and Set in its 9 functions."),
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · cases by priority, continued", title: "Eight more causes meet at least 10 functions", gap: 16,
    body: table(["Cause", "Statements", "Functions", "Cases"], more, [54, 12, 10, 24]) + bullets([
      point("Refusals naming no construct", "a failed search, a missing member or an expression with no proposed type often follows an earlier refusal that left a value of unknown type, and counts under the construct refusal its function meets (a judgement). 76 functions, 1,449 statements, meet none (measured)."),
    ]),
  }),
  slide("moved", {
    label: "Part 2 · since the last version", title: "Two causes closed, four narrowed", gap: 16,
    body: table(["Cause at aa7c768", "At aa7c768", "At b81675f", "Status, by"], moved, [46, 14, 12, 28]) + bullets([
      "Statements · functions, measured in both diagnostic censuses by the same counting. That counting puts a field reread at 828 · 17 at aa7c768, where the last version, which did not count a read after a failed inner read under the inner one, gave 3,080 · 35; it puts the record hook at 1,188 · 25, where that version's reading by hand gave 1,943 · 32.",
      "Not in the last version and measured in both censuses alike: causes 2, 5 and 8 of the table (1,772, 1,059 and 1,005 statements at aa7c768).",
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”. Of the causes closed or narrowed since the last version, the two closed took route 3 and the four narrowed route 1. Before a route is chosen, sites where TScert's code types a value it parsed as unknown are repaired."]),
  }),
  cause("record-hook", "Closed by c6e7119 · 1,188 statements, 25 functions at aa7c768", "Closed: an optional method read as a type, and bound with .bind", {
    cases: "", source: ["// blocker-indexed-optional-method: a gap, kept",
      "type Scope = { size: number; record?(key: string): number };",
      `export function apply(get: Scope["record"], key: string): number {`, "  return get?.(key) ?? 0;", "}"],
    why: "TScert's own code typed a scope's hook as TermScope[\"record\"], an optional method of a type literal read as a type, and passed scope.record?.bind(scope). An optional method's function takes its object as receiver, which the indexed access does not name, so the type reader refused the type, and the producer refused .bind on the method.",
    todo: "",
    trust: "nothing: no rule and no contract changes.",
    closed: {
      status: `${status("ok", "verified")} libraryTerm in the census; ${status("gap", "gap")} blocker-indexed-optional-method, blocker-optional-method-bind`,
      how: "route 3, a repair of type-term.mts: each hook is a field of a written function type (RecordHook and five others), passed as scope.record. Every implementation of a hook is an arrow, which uses no receiver, so each call returns, throws and writes as before. The two cases keep the refused form; the diagnostic census at b81675f meets neither refusal (measured).",
    },
  }),
  cause("inherited-key", "Closed by a03f12a · 1,112 statements, 27 functions at aa7c768", "Closed: a dictionary read at a key that may name a member of Object.prototype", {
    cases: "", note: `${status("neg", "refused, rightly")} invalid-dictionary-inherited-key; the code no longer reads so`,
    labels: ["Why it was refused", "How it was closed, and why so", "What it trusts"],
    source: ["// invalid-dictionary-inherited-key: refused, rightly", "export function inherited(k: string): number {", "  const d: { [k: string]: number } = {};", "  return d[k] ?? 0;", "}"],
    why: "a read at a string key known only at run time may find a member every object inherits from Object.prototype: under Node, inherited(\"toString\") returns a function, where the type says a number or nothing. Two such reads in tools/ were defects: an import of the name constructor took Object.prototype.constructor for a module's export, and a diagnostic's reader took variants[\"toString\"] for a list of fields.",
    todo: "",
    trust: "nothing: the refusal stays, and the code changes.",
    closed: { status: "",
      how: "route 3, a repair of tools/: a table the code builds and looks up at a run-time string is a Map, whose get and has find only the entries it was given; a decoder reading fixed keys reads them at a union of their literals. At a key the tables hold, every lookup answers as before. The diagnostic census at b81675f meets the refusal in no function (measured).",
    },
  }),
  cause("in-unknown", "Narrowed by d578dd8 · 1,282 statements, 51 functions at aa7c768", "Narrowed: k in x on unknown is admitted; the read after it stays", {
    cases: "", source: ["// blocker-in-name-object: a gap, refused at the read",
      "export function nameOf(manifest: unknown): unknown {",
      `  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;`, "}"],
    why: "k in x throws on a primitive, and after typeof x === \"object\" and x !== null an unknown stayed unknown, so the gate refused the test.",
    todo: "",
    trust: "nothing for the rule: it is proved in Lean. Closing the read would add one of two assumptions, which the owner chooses: a host read that may run any code and gives a JavaScript value, or a property of every object received at unknown.",
    closed: { narrowed: true,
      status: `${status("ok", "verified")} in-unknown-object, json-parse-manifest; ${status("gap", "gap")} blocker-in-name-object`,
      how: "route 1: each test on unknown keeps the kinds of JavaScript value it does not rule out (null, a number, an object without call code, a function …), so the test of k in x is admitted where no primitive remains. Before it, 5dfb065 repaired the code that typed a parsed package.json unknown (route 3). Open, cause 7: the read x.k after the test, since no type states the key and the read may run a getter; 24 functions, 1,016 statements.",
    },
  }),
  cause("nullable-field", "Narrowed by 05041cf · 828 statements, 17 functions at aa7c768", "Narrowed: a field reread after a guard on it", {
    cases: "", source: ["// blocker-nullable-field: verified",
      "function isList(value: Json | undefined): value is readonly Json[] {", "  return Array.isArray(value);", "}",
      "export function use(x: Dict): number {", "  if (isList(x.args)) return x.args.length;", "  return 0;", "}"],
    why: "a type guard (a function declared value is …) narrowed only an argument that is a name, and every call, the guard's own included, dropped what was known of the heap, so a second read of x.args said nothing of the first.",
    todo: "",
    trust: "nothing: both rules are proved in Lean.",
    closed: { narrowed: true,
      status: `${status("ok", "verified")} blocker-nullable-field, blocker-nullable-field-argument; ${status("gap", "gap")} guard-field-assertion`,
      how: "route 1: a call at a signature that writes no existing location keeps every heap fact, and a guard narrows a member path it tests. Open, 8 functions and 300 statements, at three sites: t.optional.map after guards negated in an || before a return (claim-text.mts, 6 functions), claim.context.forEach after Array.isArray(claim.context) (diagnostic.mts), and target.name.text after ts.isIdentifier(target.name) (fragment-statements.mts). Open outside the census: an assertion function's statement (guard-field-assertion).",
    },
  }),
  cause("array-index", "Narrowed by b276cd5 · 1,470 statements, 17 functions at aa7c768", "Narrowed: an element read in an optional chain at a number key", {
    cases: "", source: ["// blocker-callback-array-index: verified",
      "export function use(node: TypeReferenceNode, parameters: readonly TypeParameterDeclaration[]): void {",
      "  parameters.forEach((parameter, index) => {", "    const written = node.typeArguments?.[index];", "  });", "}"],
    why: "outside an optional chain, a read xs[i] at a key that is no literal index is typed as JavaScript's element read, which gives an element or undefined; inside a chain TScert's translation of the source wrote a plain member read instead, which is typed only at a literal index.",
    todo: "",
    trust: "nothing: the element read is already modelled.",
    closed: { narrowed: true,
      status: `${status("ok", "verified")} blocker-callback-array-index, optional-chain-dynamic-index`,
      how: "route 1: xs?.[i] and o?.a[i] read through the element read on the chain's present value. Open, 9 functions and 779 statements, in three forms: a write own[own.indexOf(x)], where indexOf may return −1; reads and writes of a record at keys Object.keys or Object.entries gives; literal indexes such as declarations[0] on values that, as read in the source, an earlier refusal left of unknown type (a judgement).",
    },
  }),
  cause("alias-guard", "Cause 1 · 2,052 statements, 37 functions", "A member of a node read after isTypeAliasDeclaration", {
    cases: "blocker-type-alias-guard-member",
    source: [`import * as ts from "typescript/unstable/ast";`, "export function arity(node: ts.Node): number {",
      "  return ts.isTypeAliasDeclaration(node) ? (node.typeParameters?.length ?? 0) : 0;", "}"],
    why: "the compiler's guard isTypeAliasDeclaration also accepts a JSDoc @typedef, a node of another kind (345), and TScert reads the guard by what its code accepts. Its description of the compiler's nodes gives that kind only the members every node has, so node.typeParameters is refused, as node.name is. In tools/, the reading of mapped types in type-term.mts, and (read in the source) findBlockTypes in fragment-parse.mts, which lowerFile (692 statements) reaches.",
    todo: "describe the @typedef node's members as the compiler makes them (route 1, describing external code); or a repair of tools/: a test of node.kind that excludes kind 345.",
    trust: "for the description, the @typedef node's members, audited against the compiler's code.",
  }),
  cause("optional-unbound", "Cause 2 · 1,779 statements, 12 functions", "An optional chain the producer reports as an unbound name ?.", {
    cases: "", note: `${noCase}: a cause to establish`,
    labels: ["What the census shows", "What is known", "What closing it would trust"],
    source: ["// fragment-expressions.mts, in expr: one of the 9 sites", "return {", "  k: \"new\", pos: gate.span(node), callee, args,",
      "  ...(node.typeArguments?.length ? { typeArgs: node.typeArguments.map((t) => gate.typeOf(t, t)) } : {}),", "};"],
    why: "the producer refuses the chain's test with \"unbound name ?.\": the name it gives the value a ?. tested is not in scope. Each of the 9 sites is a chain such as node.typeArguments?.length or forms?.[0], the test of a conditional inside an object spread, or under ??. The 12 functions include collect (386 statements), classBody (350), selectGlobal (306) and expr (292).",
    todo: "the forms written alone verify outside the census, the chain as a conditional's test inside a spread included, so the cause at these sites is not established (an investigation, not yet a rule). It was already in the census of aa7c768, 1,772 statements, and in no table of the last version.",
    trust: "not known before the cause is.",
  }),
  cause("number", "Cause 3 · 1,113 statements, 24 functions", "Number both called and read through its members", {
    cases: "number-call-and-members",
    source: ["// number-call-and-members: a gap", "function parse(text: string): number {", "  const n = Number(text);", "  return Number.isFinite(n) ? n : 0;", "}"],
    why: "each use alone is admitted: Number(x) through Number's call signature, Number.isFinite through its reviewed members. A function using both needs the global as a callable object with methods, a type the producer's proposals have no form for, so the library declarations that function needs are refused. In tools/, Number(atom.v) beside Number.isFinite in claim-text.mts.",
    todo: "a form for a callable object with methods, checked by the existing rules for calls and for member reads (route 1).",
    trust: "nothing new: the call signature and the members already have their contracts.",
  }),
  cause("closure-context", "Cause 4 · 1,082 statements, 16 functions", "A callback parameter whose context is a library type", {
    cases: "blocker-closure-map-context",
    source: ["export function bound(scopes: readonly ReadonlySet<string>[], name: string): boolean {",
      "  return scopes.some((scope) => scope.has(name));", "}"],
    why: "an unannotated callback parameter takes the type TypeScript gives it from its context only when that type is built from primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name; a library interface such as ReadonlySet&lt;string&gt;, Map&lt;string, string&gt; or PromiseLike is refused. lowerFile (692 statements) meets it.",
    todo: "read a context type that names a library interface as an annotation naming it would be read, with the same refusals where that reading has none.",
    trust: "nothing new: an annotation of the same type already rests on the same library declarations.",
  }),
  cause("set-map", "Cause 5 · 1,059 statements, 9 functions", "Map and Set: no binding in the slice, or instanceof of them", {
    cases: "", note: `${noCase}`,
    labels: ["Why it is not proven", "What is known", "What closing it would trust"],
    source: ["// diagnostic-gate.mts, in copied", "if (value instanceof Map) {", "  const result = new Map<unknown, unknown>();", "  for (const [key, item] of value) result.set(key, copied(item, seen));", "}"],
    why: "in diagnostic-gate.mts the gate refuses value instanceof Map and instanceof Set: no reviewed entry admits either class as the right operand of instanceof (3 functions). In the other 6 (collect, 386 statements, selectGlobal, 306, makeProbe, 193, and three more) the slice holds no binding of Map or Set where it writes new Map&lt;…&gt;() or new Set(…), and the loops over them then miss their iteration.",
    todo: "for instanceof, an entry naming the class's prototype, audited as for an imported class (route 1). For the missing binding the cause is not established: existing cases that construct and iterate both classes verify, and no small form of these census sites is written yet.",
    trust: `${trust} for instanceof: Map's and Set's constructors give their instances the standard prototype, and no code replaces Symbol.hasInstance.`,
  }),
  cause("array-view", "Cause 6 · 1,024 statements, 15 functions", "An array's method read where its type joins a record", {
    cases: "blocker-array-finally-view",
    source: ["declare const values: { value: number }[];", "export function use<T>(run: () => T): T {",
      "  try { return run(); }", "  finally { values.splice(0, 1); }", "}"],
    why: "a read of splice or flat on a value whose type TScert holds as a union of an array and a record that does not state the member is refused: a test that the value is an array keeps the record, a value of which may be an array carrying its keys. In the case, the declared array read in the finally block of a generic function is held at such a union, for a cause not yet established; in tools/, recordings.splice in files.mts.",
    todo: "keep the declared array's own type through the finally block, where nothing makes it a record.",
    trust: "nothing.",
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What stays open: causes to establish, then external code, then rules", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. Causes to establish: the chain reported as ?. (cause 2), Map and Set with no binding (5), the generic function (8), the array in a finally block (6), and the two of the second table marked no case", `${c("blocker-array-finally-view")} for 6; the others none yet, each needs its smallest refused source first`, status("gap", "not known")],
      ["2. External code described: the @typedef node's members (cause 1, or a repair testing node.kind), instanceof Map and Set (5), Array's declaration (9), node:url's two functions, the compiler's unreviewed Type methods (second table, refused until reviewed)", `${c("blocker-type-alias-guard-member")}, ${c("blocker-array-generic-annotation")}, ${c("blocker-node-url-import")}`, status("trust", "an audited description each")],
      ["3. Rules: Number's form (3), a library context type (4), the read after k in x (7), Object.entries (10)", `${c("number-call-and-members")}, ${c("blocker-closure-map-context")}, ${c("blocker-in-name-object")}, ${c("blocker-entries-mixed-overloads")}`, `${status("ok", "none")}; the read after k in x, an assumption the owner chooses`],
    ], [50, 34, 16]) + bullets([
      "The order follows the census process: sites where TScert's own code discards what it knew are repaired first (none is left among the heaviest causes), so the causes not yet established come first, and external code no contract describes is described, its trust reviewed by the owner before the merge. Within a step, by the statements blocked.",
      "The census and the diagnostic census, run once on main after the merges of these steps, measure what each gained.",
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
