/* The gap-priorities deep dive: where TScert's proofs of its own code fail,
 * from the diagnostic census, the case examples made for those failures,
 * and the cases by priority, each closed one with how and why it was
 * closed. Built with the deck kit (`make deck NAME=gap-priorities`). */
import {
  bullets, card, cards, code, color, cover, point, slide, stat, status, table,
  type Deck, type Slide, type Status,
} from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** A case's name, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
const trust = status("trust", "trust change");

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
  ["1", "A field holding an object, reread after a test of it", "3,080", "35", `${status("gap", "gap")} ${c("blocker-nullable-field")}`],
  ["2", "An optional method read as a type, and bound with .bind", "1,943", "32", `${status("gap", "gap")} ${c("blocker-indexed-optional-method")}, ${c("blocker-optional-method-bind")}`],
  ["3", "A numeric key not proved an array index", "1,470", "17", `${status("gap", "gap")} ${c("blocker-callback-array-index")}`],
  ["4", "A key test k in x on an operand typed unknown", "1,282", "51", `${status("gap", "gap")} ${c("in-primitive-refused")}, ${c("blocker-in-name-object")}`],
  ["5", "A dictionary read at a key that may name a member of Object.prototype", "1,112", "27", `${status("neg", "refused, rightly")} ${c("invalid-dictionary-inherited-key")}`],
  ["6", "A callback parameter whose context is a library type", "1,063", "16", `${status("gap", "gap")} ${c("blocker-closure-map-context")}`],
  ["7", "A member of a type alias read after isTypeAliasDeclaration", "1,058", "26", `${status("gap", "gap")} ${c("blocker-type-alias-guard-member")}`],
  ["8", "An array's method read where its type joins a record", "1,024", "15", `${status("gap", "gap")} ${c("blocker-array-finally-view")}`],
  ["9", "Array's declaration, read for an annotation Array&lt;T&gt;", "868", "10", `${status("gap", "gap")} ${c("blocker-array-generic-annotation")}`],
  ["10", "Object.entries, whose overloads are generic and plain", "860", "28", `${status("gap", "gap")} ${c("blocker-entries-mixed-overloads")}`],
];

const more: [string, string, string, string][] = [
  ["A spread of a value that may not be a plain object (a module namespace)", "724", "18", status("gap", "no case")],
  ["Number both called and read through its members", "674", "20", `${status("gap", "gap")} ${c("number-call-and-members")}`],
  ["A for statement's condition read after ts.isForStatement on a union of loops", "663", "22", status("gap", "no case")],
  ["A method of the compiler's Type TScert has not reviewed (isUnionType …)", "660", "17", `${status("neg", "refused")} ${c("invalid-compiler-api-sync-guard")}`],
  ["A write that may add a key to an object others hold", "626", "25", `${status("gap", "gap")} ${c("blocker-loop-key-adding-write")}`],
  ["The library type ArrayBufferLike, at a site the census does not locate", "452", "20", status("gap", "no case")],
  ["fileURLToPath and pathToFileURL of node:url", "435", "19", `${status("gap", "gap")} ${c("blocker-node-url-import")}`],
  ["An assignment to a module's let", "387", "42", `${status("gap", "gap")} ${c("blocker-module-assignment")}`],
  ["import.meta", "190", "25", `${status("gap", "gap")} ${c("blocker-import-meta")}`],
];

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and most functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and turns each cause into a small case example. Part 2 ranks those cases by how much code they block, and shows for each closed case how and why it was closed, and for each of the heaviest open ones what closing it needs.",
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
    label: "Part 1 · where proofs fail", title: "Two censuses of main at aa7c768 (2026-10-27)", gap: 22,
    body: cards([
      stat("204 of 510", `functions of tools/ ${status("ok", "verified")} by the census, 1,485 of 13,478 statements (11.0%, measured); 189 of 499 at the census before it, of commit 83cdb42`, "ok"),
      stat("399", "functions the diagnostic census takes to their end (below); 44 stop at regions it cannot examine, 66 at the 300 s limit of a stage, 1 at a failure of the compiler interface (measured)"),
      stat("23.9%", "coverage with holes: 3,220 statements outside the regions the diagnostic census had to assume, in copies that pass its checks under those assumptions; not verified (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied, with what it uses, into a file of its own (a slice) and run through TScert (make census). A refused function stops at its first reason. The verified census ran at a0ffcd7, whose tools/ is aa7c768's."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified."),
      point("Causes", "every refusal naming one construct counts, at whatever stage: the gate, the type reader, the producer, or the search for a proof. Each cause is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by their number. The function lowerFile, 692 statements, meets four of the ten heaviest."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example", gap: 20,
    body: code(["// blocker-node-url-import.ts. Census functions: family-activation.mts#activeGuards, …",
      `import { fileURLToPath } from "node:url";`,
      "export function pathOf(url: string): string {", "  return fileURLToPath(url);", "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from the census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("Which causes get one", `every cause meeting at least 10 functions, where its smallest source is found; three have none yet (marked no case). Earlier censuses made most of the cases the next slides name; five are made from this census: ${c("blocker-type-alias-guard-member")}, ${c("blocker-indexed-optional-method")}, ${c("blocker-optional-method-bind")}, ${c("blocker-node-url-import")} and ${c("blocker-array-generic-annotation")}.`),
      point("Closing a case", "a fix makes it verify, and the census copies of its functions then pass that refusal and stop at the next."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at aa7c768", title: "The ten causes that block the most code; none closed", gap: 16,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [4, 46, 11, 10, 29]) + bullets([
      "A function blocked by several causes counts under each, so the columns do not add up. The statements and functions are measured.",
    ]),
  }),
  slide("priority-more", {
    label: "Part 2 · cases by priority, continued", title: "Nine more causes meet at least 10 functions", gap: 16,
    body: table(["Cause", "Statements", "Functions", "Cases"], more, [54, 12, 10, 24]) + bullets([
      point("Refusals naming no construct", "a failed search, or an expression with no proposed type, often follows an earlier refusal that left a value of unknown type: in the 202 functions that also meet a construct refusal it counts under that one (a judgement). The 79 that meet none, 2,058 statements, spread over forms of at most 8 functions each (measured)."),
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”. The closed causes took route 1, with one runtime check (route 2) in the front end's check of an installed file; Object.getPrototypeOf took route 5 (its slide comes last but one). Before a route is chosen, sites where TScert's code types a value it parsed as unknown are repaired."]),
  }),
  cause("nullable-field", "Cause 1 · 3,080 statements, 35 functions", "A field holding an object, reread after a test of it", {
    cases: "blocker-nullable-field",
    source: ["declare function isList(value: Json | undefined): value is readonly Json[];",
      "export function use(x: Dict): number {", "  if (isList(x.args)) return x.args.length;", "  return 0;", "}"],
    why: "what TScert knows a field holds after a test is a union of primitive values, as the producer's refusal states. A test of x.args, by a function declared as a type guard (value is …) or for truthiness, tells nothing of a later read of x.args when it holds an object, so x.args.length is refused; in tools/, at reads such as atom.required.map in claim-text.mts.",
    todo: "carry the test's narrowing of a field holding an object to its reread, where no code between them can write the field: no call, no write through another reference.",
    trust: "nothing new.",
  }),
  cause("record-hook", "Cause 2 · 1,943 statements, 32 functions", "An optional method read as a type, and bound with .bind", {
    cases: "blocker-indexed-optional-method, blocker-optional-method-bind",
    source: ["type Scope = { size: number; record?(key: string): number };",
      `export function apply(get: Scope["record"], key: string): number {`, "  return get?.(key) ?? 0;", "}"],
    why: "TScert's own code: expandMapped (type-term.mts) takes its scope's hook as record?: TermScope[\"record\"], and typeTerm passes it scope.record?.bind(scope). An optional method's function takes its object as receiver, which the indexed access does not name, so the type reader refuses the type (32 functions), and the producer refuses .bind on the method (22). libraryTerm, verified at 83cdb42, is refused by it.",
    todo: "a repair of the code first (route 3): the hook's function type written out, and an arrow (k, f) =&gt; scope.record?.(k, f) passed for it; otherwise, reading the indexed access as the method's function at its object.",
    trust: "nothing.",
  }),
  cause("array-index", "Cause 3 · 1,470 statements, 17 functions", "A numeric key not proved an array index", {
    cases: "blocker-callback-array-index",
    source: ["export function use(node: TypeReferenceNode, parameters: readonly TypeParameterDeclaration[]): void {",
      "  parameters.forEach((parameter, index) => {", "    const written = node.typeArguments?.[index];", "  });", "}"],
    why: "a read xs[i] is typed only at a key proved an array index, an integer from 0; ordinary numeric properties are not modelled. The index forEach passes its callback, and a counter a loop keeps, carry no such fact at the read.",
    todo: "state that forEach passes its callback an array index, and that a counter from 0 by steps of 1 is one, and use the fact at the read.",
    trust: "for forEach, a statement in its audited contract that the index it passes is an array index of the array it iterates.",
  }),
  cause("in-unknown", "Cause 4 · 1,282 statements, 51 functions; narrowed by cc04cef–960767f", "A key test k in x on an operand typed unknown", {
    cases: "", source: ["// blocker-in-name-object: a gap",
      "export function nameOf(manifest: unknown): unknown {",
      `  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;`, "}"],
    why: "k in x throws on a primitive, and after typeof x === \"object\" and x !== null an unknown stays unknown: no type of the model names every non-null object. Every function owns a key name, so \"name\" in x tells nothing of x where x may be a function; where x cannot be one the gate admits the test, and the refusal comes later, when the function is translated for the proof checker.",
    todo: "",
    trust: `${trust}, in the caller contract (what TScert assumes of the values a function receives from code it does not check): a value received at a record type reads inherited fields as it would own ones.`,
    closed: { narrowed: true,
      status: `${status("ok", "verified")} in-function-key; ${status("gap", "gap")} in-primitive-refused, blocker-in-name-object`,
      how: "closed (route 1): k in o for a key a function owns or inherits (name, call …), where o holds no function. Open: 24 of the 51 functions test a package.json the code parses and types unknown, where the parse gives a JSON value: a repair of the code (route 3). The others test values typed unknown for other reasons (decoded documents, compiler nodes, a client, a child process, this): the same repair where the code parsed the value, else a type naming every non-null object.",
    },
  }),
  cause("inherited-key", "Cause 5 · 1,112 statements, 27 functions", "A dictionary read at a key that may name a member of Object.prototype", {
    cases: "", note: `${status("neg", "refused, rightly")} invalid-dictionary-inherited-key`,
    labels: ["Why it is refused", "What closing it needs", "What it trusts"],
    source: ["export function inherited(k: string): number {", "  const d: { [k: string]: number } = {};", "  return d[k] ?? 0;", "}"],
    why: "a read at a string key known only at run time may find a member every object inherits from Object.prototype: under Node, inherited(\"toString\") returns a function, where the type says a number or nothing. In tools/, table.helpers[key] and declaring[entry.name] in family-activation.mts, atom[key] in claim-text.mts.",
    todo: "the refusal is right, so the route is a repair of TScert's code (route 3): a lookup that cannot find an inherited member, such as a Map; which form tools/ takes is open.",
    trust: "nothing: the refusal stays, and the code changes.",
  }),
  cause("closure-context", "Cause 6 · 1,063 statements, 16 functions", "A callback parameter whose context is a library type", {
    cases: "blocker-closure-map-context",
    source: ["export function bound(scopes: readonly ReadonlySet<string>[], name: string): boolean {",
      "  return scopes.some((scope) => scope.has(name));", "}"],
    why: "an unannotated callback parameter takes the type TypeScript gives it from its context only when that type is built from primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name; a library interface such as ReadonlySet&lt;string&gt;, Map&lt;string, string&gt; or PromiseLike is refused (measured: 16 functions).",
    todo: "read a context type that names a library interface as an annotation naming it would be read, with the same refusals where that reading has none.",
    trust: "nothing new: an annotation of the same type already rests on the same library declarations.",
  }),
  cause("alias-guard", "Cause 7 · 1,058 statements, 26 functions", "A member of a type alias read after isTypeAliasDeclaration", {
    cases: "blocker-type-alias-guard-member",
    source: [`import * as ts from "typescript/unstable/ast";`, "export function arity(node: ts.Node): number {",
      "  return ts.isTypeAliasDeclaration(node) ? (node.typeParameters?.length ?? 0) : 0;", "}"],
    why: "the compiler's guard isTypeAliasDeclaration also accepts a JSDoc @typedef, a node of another kind (345), and TScert reads the guard by what its code accepts. Its description of the compiler's nodes gives that kind only the members every node has, so node.typeParameters is refused, as node.name is. e93eb63 added such a read to the reading of mapped types, which typeTerm and 20 other functions of type-term.mts reach.",
    todo: "describe the @typedef node's members as the compiler makes them (route 1, describing external code); or a repair of tools/: a test of node.kind that excludes kind 345.",
    trust: "for the description, the @typedef node's members, audited against the compiler's code.",
  }),
  cause("array-view", "Cause 8 · 1,024 statements, 15 functions", "An array's method read where its type joins a record", {
    cases: "blocker-array-finally-view",
    source: ["declare const values: { value: number }[];", "export function use<T>(run: () => T): T {",
      "  try { return run(); }", "  finally { values.splice(0, 1); }", "}"],
    why: "a read of splice or flat on a value whose type TScert holds as a union of an array and a record that does not state the member is refused: a test that the value is an array keeps the record, a value of which may be an array carrying its keys. In the case, the declared array read in the finally block of a generic function is held at such a union, for a cause not yet established; in tools/, recordings.splice in files.mts.",
    todo: "keep the declared array's own type through the finally block, where nothing makes it a record.",
    trust: "nothing.",
  }),
  cause("mapped", "Closed by e93eb63, da191e7 and 64f1871 · mapped types, which blocked 51 functions at 83cdb42", "Closed: mapped types whose field type is T[P], the type of T's field P", {
    cases: "", source: ["// blocker-readonly-record: verified",
      "export function joined(files: Readonly<Record<string, string>>): string {",
      "  let out = \"\";", "  for (const [, text] of Object.entries(files)) out += text;", "  return out;", "}"],
    why: "TScert read a mapped type {[P in K]: V} only where V does not mention P. Partial, Readonly, Required and Pick write T[P], so the gate refused them. In tools/, Readonly met 45 of the 51 functions (measured).",
    todo: "",
    trust: "nothing: it is a reading of a type annotation, not a contract. Still refused, each with its case: T[P] at a union, an array, a callable, a class, a record with a method, or a shape that reaches itself; over a written key union; and Required (removing ?) over an optional field that may hold undefined, whose meaning depends on the compiler option exactOptionalPropertyTypes.",
    closed: {
      status: `${status("ok", "verified")} blocker-readonly-record, written-partial-argument, mapped-identity-named`,
      how: "route 1, support: rules mapped-identity and mapped-pick. Over keyof T the type is T's fields and index signatures; over Pick's K, bounded by keyof T, the fields K names; each marker ? and readonly is added, removed or kept from T, as written. A named interface or alias is read as its fields, bases included. The diagnostic census at aa7c768 meets no mapped-type refusal, against 96 at 83cdb42 (measured).",
    },
  }),
  cause("bytes", "Closed by 787002e and a0ffcd7 · Buffer, which blocked 72 functions at 83cdb42", "Closed: Node's file system and Buffer, through audited entries", {
    cases: "", source: ["// blocker-node-buffer-contract: verified", `import { statSync } from "node:fs";`, "export function use(path: string): number { return statSync(path).size; }"],
    why: "the node:fs functions with no contract (statSync among them) were read through their declarations, which reach Buffer: Buffer.from returns Buffer&lt;ImplicitArrayBuffer&lt;TArrayBuffer&gt;&gt;, a conditional type over a type parameter, which the gate refuses.",
    todo: "",
    trust: `${trust}, approved by the owner: an entry each for statSync, mkdirSync, chmodSync, writeFileSync, readFileSync, readdirSync, Buffer.from, Buffer.compare and TextDecoder, audited against Node 25.2.1; every Uint8Array and Buffer is a host object with its standard prototype chain and its elements alone as own properties.`,
    closed: {
      status: `${status("ok", "verified")} blocker-node-buffer-contract, node-fs-stat, node-bytes-buffer`,
      how: "route 1, support: with an entry at the arguments tools/ passes, a function's declaration is not read. Buffer and Uint8Array are read at types an overlay states: a byte array, whose bytes and length only the host's own reads give. Still refused: Node's declaration NonSharedBuffer, which writes Buffer with type arguments (6 functions); 20 functions meet ArrayBufferLike through declarations not yet located (no case).",
    },
  }),
  cause("hash", "Closed by 395a66d and a0ffcd7 · Node's crypto declarations, which blocked 44 functions at 83cdb42", "Closed: Node's crypto hash read through one audited entry", {
    cases: "", source: ["// blocker-node-hash-contract: verified", `import { createHash } from "node:crypto";`, `export function use(s: string): string { return createHash("sha256").update(s).digest("hex"); }`],
    why: "createHash had no contract, so the gate read Node's declaration of it and every type that declaration names; HashOptions extends the stream type TransformOptions, where TypeScript infers a member's type with no declaration to check it against.",
    todo: "",
    trust: `${trust}: the entry, audited against Node 25.2.1's hash.js; every Hash keeps Node's prototype, which holds update and digest as data properties.`,
    closed: {
      status: `${status("ok", "verified")} blocker-node-hash-contract, node-crypto-hash`,
      how: "route 1, support: createHash at \"sha256\", update at a string or a Uint8Array (a Buffer is one), digest at \"hex\", each stating no footprint, so it may change any location; another algorithm or encoding is refused. The diagnostic census at aa7c768 meets no refusal in Node's crypto declarations; 3 functions of unchecked.mts still meet Node's stream declarations (measured).",
    },
  }),
  cause("instanceof", "Closed by 0fd783b · instanceof, which blocked 26 functions at 83cdb42", "Closed: instanceof of a class another module declares", {
    cases: "", source: ["// blocker-instanceof-imported-class: verified",
      `import { IoFailure } from "./blocker-instanceof-imported-class-failure.ts";`,
      "export function wrap(operation: string, run: () => string): string {",
      "  try { return run(); }", "  catch (error) { throw error instanceof IoFailure ? error : new IoFailure(operation); }", "}"],
    why: "x instanceof C narrows x to C's instances, which needs the prototype C's constructor gives them. The gate read that only for a class declared at the file's top level; the front end tests its own error classes (IoFailure, CompilerFailure …), which other modules declare.",
    todo: "",
    trust: `${trust}: the imported class's binding holds the class its declaration creates, and the lookup of Symbol.hasInstance along its prototype chain finds only data properties yielding the standard method.`,
    closed: {
      status: `${status("ok", "verified")} blocker-instanceof-imported-class, instanceof-class-value-import`,
      how: "route 1, support: the test a local class gets, for a class TScert checks in another source module, free of TypeScript errors and suppressions, whose base is nothing, Error or another such class. The declaring module may use the class only to construct it, test with it or read a member; passing it on or writing to it, which could replace its prototype or install a hook, is refused. Three later commits refuse eight programs that broke the first version's assumptions (a replaced prototype, a suppressed error, other spellings and aliases, code in export default, extends or a static setter); six are new cases run under Node. After it, 9 functions test a caught error, typed unknown, with instanceof and read its fields: refused, rightly, since an object gets C's prototype without C's constructor running (instanceof-unknown-refused).",
    },
  }),
  cause("error", "Closed by 940af14, b2d7d97 and 8a145aa · Error's options, which blocked 14 functions at 83cdb42", "Closed: Error's options argument, and an Error returned at its type", {
    cases: "", source: ["// blocker-error-options-return: verified", "export function use(): Error {", `  return new Error("failed", { cause: "reason" });`, "}"],
    why: "TScert's contract for Error stated its message argument alone, and TypeScript's Error declares name, which TScert's model of an error held nowhere, so no error met the annotation Error. By ECMAScript's Error constructor (its step InstallErrorCause), the host checks whether the options object has a property cause and copies it to the new error.",
    todo: "",
    trust: `${trust}, approved by the owner: the host's Error constructor follows ECMAScript's description; Error.prototype holds name as a data property whose value is \"Error\" throughout execution.`,
    closed: {
      status: `${status("ok", "verified")} blocker-error-options, blocker-error-options-return, blocker-error-super-options-return`,
      how: "route 1, support: new Error(m, o), Error(m, o) and super(m, o) at options { readonly cause?: unknown }, and an error holding message and name as strings on the object the model inserts as its prototype, which meets TypeScript's Error. The rewrite of library-globals.mts's errorInstance that came with it is refused: the search finds no proof for its array of fields, built by a local helper (1 function).",
    },
  }),
  cause("sep", "Closed by aa3c69a · sep, which blocked 29 functions", "Closed: the constant sep of node:path", {
    cases: "", source: [`import { sep } from "node:path";`, "export function use(path: string): string[] { return path.split(sep); }"],
    why: `Node's declarations make the module one object, whose interface declares readonly sep: "\\\\" | "/". The gate reads an import from a Node module as an annotated constant, function or class, or through a contract, and the contracts listed functions only.`,
    todo: "",
    trust: `${trust}: sep is a data property of the module's object that no code writes, an assumption.`,
    closed: {
      status: `${status("ok", "verified")} blocker-node-path-sep`,
      how: "route 1, support: a contract entry for a module constant, naming the property declaration exactly as reviewed and stating its type, with no parameters and no effect (rule library-module-constant).",
    },
  }),
  cause("globals", "Closed by aa3c69a · globals, which blocked 30 functions", "Closed: five globals, each an audited contract", {
    cases: "", source: ["// library-math-random: verified",
      "export function rolls(sides: number[]): number[] {", "  return sides.map((n) => Math.ceil(Math.random() * n));", "}"],
    why: "a global of JavaScript's standard library is read only through a contract that lists its exact declaration. Math.random, Object.hasOwn, process.execArgv, process.platform and process.arch had none.",
    todo: "",
    trust: `${trust}: each entry, and that no code replaces process.execArgv or writes a non-string into it. WeakMap and WeakSet still need a contract for a class read through its members (${c("blocker-weakmap")}, a gap case).`,
    closed: {
      status: `${status("ok", "verified")} library-math-random, object-has-own, node-process-platform`,
      how: "route 1, support: one audited entry each, no new form. Object.hasOwn converts a string, number or symbol key without running code and writes nothing; Math.random writes nothing a program reaches; process.execArgv is read as process.argv is; platform and arch are strings.",
    },
  }),
  slide("prototype", {
    label: "Library globals · route 5", title: "Object.getPrototypeOf, confined to a host boundary", gap: 16,
    body: cards([
      card("The use", "The compiler channel (compiler-channel.mts), the front end's link to TypeScript's compiler process, checks and wraps the six methods by which the TypeScript package's private client sends a request, on the client's class prototype."),
      card("Why no other route", "An entry (o) =&gt; object | null is unsound: Array.isArray narrows getPrototypeOf([]) to an array whose writes reach every array; instanceof narrows a prototype to an instance without its fields. No rewrite avoids it: reading a method through the client itself may run a getter, code TScert does not see."),
      card("What it guarantees", "The wrapper sends each request and returns its answer, or a repeated query's earlier one (a stated conjecture). The caller's callback only runs code around that call: it cannot replace an answer or hide a failure."),
    ]) + code(["// tools/client-prototype.mts: the two functions that read the prototype, refused themselves",
      "export function clientHasMethod(api: API, member: RequestMember): boolean",
      "export function guardClientRequests(api: API, around: (member, receiver, args, send) => void): void"]) + bullets([
      point("How callers verify", `an imported function is read at its stated signature, so the channel is verified against these two (API is the package's class of a compiler process; RequestMember names the six methods); the boundary's own code is reported refused. ${status("ok", "verified")} blocker-client-prototype; ${status("neg", "refused")} blocker-client-prototype-forged, a fake API value.`),
      point("Status", `narrowed, not closed: the channel's functions stop at an earlier refusal, an import of a class whose type parameter has a default, here API (8 functions, measured). The other use, in diagnostic-gate.mts, stays refused (3 functions). ${trust}: the boundary's code meets its two signatures, given facts audited against the TypeScript package's code. Unlike a trusted unit (route 6), it is not exempted: its functions are reported refused.`),
    ]),
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "What stays open: TScert's own code first, then external code, then rules", gap: 20,
    body: table(["Step", "Cases", "Trust"], [
      ["1. Repairs of TScert's code: the record hook (cause 2), a parsed package.json typed unknown (24 functions of cause 4), dictionary reads at string keys (cause 5)", `${c("blocker-indexed-optional-method")}, ${c("blocker-optional-method-bind")}, ${c("blocker-in-name-object")}, ${c("invalid-dictionary-inherited-key")}`, status("ok", "none")],
      ["2. External code described: the @typedef node's members (cause 7), node:url's two functions, Array's declaration (cause 9)", `${c("blocker-type-alias-guard-member")}, ${c("blocker-node-url-import")}, ${c("blocker-array-generic-annotation")}`, status("trust", "an audited description each")],
      ["3. Rules: a reread field (cause 1), forEach's index (3), a library context type (6), the array in a finally block (8), Object.entries (10), a type naming every non-null object (rest of 4)", `${c("blocker-nullable-field")}, ${c("blocker-callback-array-index")}, ${c("blocker-closure-map-context")}, ${c("blocker-array-finally-view")}, ${c("blocker-entries-mixed-overloads")}, ${c("in-primitive-refused")}`, `${status("ok", "none")}; forEach's index stated in its contract`],
    ], [50, 34, 16]) + bullets([
      "The order follows the census process: sites where TScert's own code discards what it knew are repaired first, and external code no contract describes is described, its trust reviewed by the owner before the merge. Within a step, by the statements blocked.",
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
