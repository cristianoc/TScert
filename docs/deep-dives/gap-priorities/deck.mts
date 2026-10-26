/* The gap-priorities deep dive: where TScert's proofs of its own code fail,
 * the case examples made for those failures, and the cases by priority, each
 * closed one with how and why it was closed. Built with the deck kit
 * (`node dev/deck-cli.mts gap-priorities`). */
import { execFileSync } from "node:child_process";
import {
  bullets, card, cards, code, color, cover, inline, point, record, recordSlide, slide, status, table,
  type Deck, type Slide, type Status,
} from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** A case's name, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
const trust = status("trust", "trust change");

/** An aspect's slide: its case's code, then why it is refused, what proving
 * it needs and what that would trust, or, for a closed one, how it was
 * closed. */
function aspect(id: string, n: number, title: string, weight: string, o: {
  cases: string; source: string[]; why: string; todo: string; trust: string;
  closed?: { status: string; how: string };
}): Slide {
  const labels = o.closed ? ["Why it was refused", "How it was closed, and why so", "What it trusts"]
    : ["Why it is not proven", "What proving it needs", "What it would trust"];
  return slide(id, {
    label: `Aspect ${n} · ${weight}`, title, gap: 18,
    note: o.closed ? o.closed.status : `${status("gap", "gap")} ${o.cases}`,
    body: code(o.source) + bullets([point(labels[0] ?? "", o.why), point(labels[1] ?? "", o.closed ? o.closed.how : o.todo), point(labels[2] ?? "", o.trust)]),
  });
}

const prio: [string, string, string, string, string, [Status, string]][] = [
  ["1", "Mapped types naming their key: Readonly, Pick, Partial", "4,374", "38", c("written-partial-argument-refused"), ["gap", "open"]],
  ["2", "Standard-library and Node globals with no contract", "3,112", "30", `${c("library-math-random")}, ${c("blocker-weakmap")}`, ["ok", "partly closed: 5 globals"]],
  ["3", "The constant sep of node:path", "3,055", "29", c("blocker-node-path-sep"), ["ok", "closed"]],
  ["4", "Compiler-interface members with no contract", "2,637", "10", c("invalid-compiler-api-view-member"), ["gap", "open"]],
  ["5", "The options argument of Error", "2,447", "11", `${c("blocker-error-super-options")}, ${c("blocker-error-options")}`, ["gap", "open"]],
  ["6", "Node's createHash", "1,055", "41", c("blocker-node-hash-contract"), ["gap", "open"]],
  ["7", "Node's Buffer, reached from node:fs", "681", "58", c("blocker-node-buffer-contract"), ["gap", "open"]],
];

/** The commit that closed the globals and sep cases, as its record states it. */
const closing = record(execFileSync("git", ["log", "-1", "--format=%B", "aa3c69a"], { encoding: "utf8" }), "aa3c69a");

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and most functions are refused. Part 1 finds where the proofs fail, past the first refusal, and turns each cause into a small case example. Part 2 ranks those cases by how much code they block, and shows for each closed case how and why it was closed, and for each open one what closing it needs.",
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert works, in three cards", gap: 28,
    body: cards([
      card("Verified, refused", "TScert verifies a function when it proves it safe: every value it reads, writes or returns has its declared type. Otherwise it refuses it, naming a location and a reason. The first stage, the <b>gate</b>, reads the TypeScript source and refuses what lies outside the language TScert admits; the later stages search for the proof and check it."),
      card("Contract", "TScert's reviewed description of code it does not check itself: a function of JavaScript's standard library, of Node, or of TypeScript's compiler interface, each listed with its exact declaration and audited by hand. A contract is an assumption the result rests on: adding one widens what TScert trusts. A library global with no contract is refused; a function imported from a library with no contract is read through its declaration's written types."),
      card("Case, gap case", "A <b>case</b> is a small TypeScript file with the outcome TScert must give it, checked by the test suite (make suite). A <b>gap case</b> is one TScert refuses for want of a rule or a contract, though the program is safe: it turns into a verified case once the missing piece is added."),
    ]),
  }),
  slide("find", {
    label: "Part 1 · where proofs fail", title: "The census, run past the first refusal", gap: 22,
    body: bullets([
      point("The census", "each top-level function of tools/ is copied into a file of its own and run through TScert. At commit 963ffa4 (2026-10-24), 178 of 490 functions are verified and 312 refused (measured)."),
      point("Past the first refusal", "a refused function stops at its first reason. A diagnostic tool rewrites the copy crudely at each refusal and runs it again, so that later reasons show up too; its run finished for 210 of the 312 functions (measured). Every reason it meets, first or later, is kept."),
      point("Aspects", "the gate's reasons are grouped by cause, an aspect. Each aspect is weighted by the statements (an if, a return, an assignment …) of the functions it blocks, and by the number of those functions. The later stages' reasons are left out: they vary from function to function."),
      point("One caveat", "the function collectDeclarations has 2,334 statements and meets five of the heaviest aspects, so it dominates their statement weight; the function counts have no such bias."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy aspect becomes a small case example", gap: 20,
    body: code(["// blocker-node-path-sep.ts. Census functions: declaration-graph.mts#originOf, …",
      `import { sep } from "node:path";`,
      "export function use(path: string): string[] { return path.split(sep); }"]) + bullets([
      point("A case example", "is the smallest source with the aspect's refusal, and its header lists the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("Which aspects get one", "every aspect blocking more than 1,000 statements or more than 40 functions: nine aspects. Seven of them had gap cases in the suite, nine cases among them; the other two get one first (next slide)."),
      point("Closing a case", "a fix makes it verify, and the census copies of its functions then pass that refusal and stop at the next."),
    ]),
  }),
  slide("uncovered", {
    label: "Part 1 · aspects with no case yet", title: "Two heavy aspects need a case example first", gap: 22,
    body: table(["Aspect", "Statements", "Functions", "The refusal"], [
      ["An indexed access type T[\"f\"] whose field f is an optional function", "2,698", "2", "the gate reads T[\"f\"] only as the field's type as written; here TypeScript gives it with | undefined added, a type no declaration writes"],
      ["A key test in on a function value", "1,068", "11", "`in` with the key 'name': the refusal reads the key as one every function holds, own or from Function.prototype; the rule that would admit the test is to be worked out with its case"].map(inline),
    ], [30, 12, 10, 48]) + bullets([
      "The first is met by collect and collectDeclarations only; the second by functions of declaration-graph.mts and fragment-parse.mts (measured).",
      `The same refusal over a method has a case (${c("blocker-api-indexed-method")}); over an optional field, and for the in test, there is none yet.`,
      "Left out: the reasons of the stages after the gate, such as an expression with no proof of its type (50 functions), whose causes differ from function to function; and “no functions in file” (22 functions, 1,000 statements), a report on a file, not on a construct.",
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, weights at 963ffa4", title: "Seven aspects, nine cases, ranked by the code they block", gap: 18,
    body: table(["#", "Aspect", "Statements", "Functions", "Cases", "Status"],
      prio.map(([n, a, st, f, cs, [k, w]]) => [n, a, st, f, cs, status(k, w)]), [4, 32, 11, 9, 28, 16]) + bullets([
      "An aspect's statements and functions are those of the functions it blocks at any point; aspects overlap (measured).",
      `Closed: every case of the aspect verifies; partly closed: some do. The cases listed are those the ranking picked for each aspect; ${c("library-math-random")} replaces aspect 2's ${c("library-global-unreviewed")}, the same program once its contract was added. The weights still count the functions the closed cases blocked.`,
    ]),
  }),
  slide("routes", {
    label: "Part 2 · how a refusal is decided", title: "Eight routes, the first that works at acceptable cost", gap: 16,
    body: table(["Route", "When it applies"], [
      ["1. Support", "a rule or contract admits the construct: it has useful reach in the census and a proportionate implementation"],
      ["2. A runtime check", "an executable check establishes the whole property, also after later writes; checking a value's shape says nothing of what code writes"],
      ["3. A repair", "the refusal exposes a defect in TScert's code, which changes"],
      ["4. Avoidance", "support is costly, the construct rare, and a rewrite is observationally equivalent; the construct stays refused"],
      ["5. A host boundary", "a necessary operation on an external service moves to the smallest module, whose signatures only the host value inhabits"],
      ["6. A trusted unit", "the project's owner approves exempting a narrow unit of TScert's code from checking, reported with its contract; never a fallback"],
      ["7. A proof", "a proof in Lean, the proof assistant TScert's checker is proved in, where the model of JavaScript it needs exists or has wider value"],
      ["8. The refusal stays", "no route works at acceptable cost; the census reports it"],
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”. The closed cases took route 1; Object.getPrototypeOf took route 5."]),
  }),
  aspect("sep", 3, "Closed: the constant sep of node:path", "3,055 statements, 29 functions", {
    cases: "", source: [`import { sep } from "node:path";`, "export function use(path: string): string[] { return path.split(sep); }"],
    why: `Node's declarations make the module one object, whose interface declares readonly sep: "\\\\" | "/". The gate reads an import from a Node module as an annotated constant, function or class, or through a contract, and the contracts listed functions only. 27 of the 29 functions met it first (measured).`,
    todo: "",
    trust: `${trust}: sep is a data property of the module's object that no code writes, an assumption.`,
    closed: {
      status: `${status("ok", "verified")} blocker-node-path-sep`,
      how: "route 1, support: a contract entry for a module constant, naming the property declaration exactly as reviewed and stating its type, with no parameters and no effect (rule library-module-constant). In the census, isHostFile and guardOfExport pass sep and stop at later aspects, crypto's hash options and Readonly (measured).",
    },
  }),
  aspect("globals", 2, "Closed: five globals, each an audited contract", "3,112 statements, 30 functions", {
    cases: "", source: ["// library-math-random: verified",
      "export function rolls(sides: number[]): number[] {", "  return sides.map((n) => Math.ceil(Math.random() * n));", "}",
      "// object-has-own: verified",
      "export function owns(table: { readonly [key: string]: number }, key: string): boolean {",
      "  return Object.hasOwn(table, key);", "}"],
    why: "a global of JavaScript's standard library is read only through a contract that lists its exact declaration. Math.random, Object.hasOwn (14 functions), process.execArgv (12), process.platform and process.arch had none.",
    todo: "",
    trust: `${trust}: each entry, and that no code writes process.execArgv. Still open in this aspect: WeakMap and WeakSet, which need a contract for a class read through its members (blocker-weakmap); Uint8Array goes with Buffer (aspect 7).`,
    closed: {
      status: `${status("ok", "verified")} library-math-random, object-has-own, node-process-platform · ${status("gap", "gap")} blocker-weakmap`,
      how: "route 1, support: one audited entry each, no new form. Object.hasOwn converts a string, number or symbol key without running code and writes nothing; Math.random writes nothing a program reaches; process.execArgv is read as process.argv is, a readonly array of strings; platform and arch are strings. A review of the change found Object.getPrototypeOf unsound as an entry (slide “Object.getPrototypeOf”).",
    },
  }),
  recordSlide("closing-record", closing, ["Rule added (library modules: a constant)", "Effect"]),
  slide("prototype", {
    label: "Aspect 2 · one use in tools/, route 5", title: "Object.getPrototypeOf, confined to a host boundary", gap: 16,
    body: cards([
      card("The use", "The compiler channel (compiler-channel.mts), the front end's link to TypeScript's compiler process, checks and wraps the six request methods of its private client, on the client's class prototype: 8 functions reached it (measured)."),
      card("Why no other route", "An entry (o) =&gt; object | null is unsound: Array.isArray narrows getPrototypeOf([]) to an array whose writes reach every array; instanceof narrows a prototype to an instance without its fields. No rewrite avoids it: a read through the client can run a getter."),
      card("What it prevents", "A caller's callback cannot supply an answer: the boundary returns each itself, rethrows a failed request, and refuses a send kept for later."),
    ]) + code(["// tools/client-prototype.mts: the two functions that read the prototype, refused themselves",
      "export function clientHasMethod(api: API, member: RequestMember): boolean",
      "export function guardClientRequests(api: API, around: (member, receiver, args, send) => void): void"]) + bullets([
      point("How callers verify", `an imported function is read at its stated signature, so the channel is verified against these two; the boundary's own code is reported refused. They take the API, a value only the package makes, and return neither client, prototype, method nor a way to answer. ${status("ok", "verified")} blocker-client-prototype; ${status("neg", "refused")} blocker-client-prototype-forged.`),
      point("Status", `narrowed, not closed. The channel's 8 functions stop at an earlier refusal: an import of a class whose type parameter has a default, here API (measured; 7 functions, 70 statements in the 963ffa4 data). ${trust}: the boundary's code, TScert's own and unchecked, meets its two signatures, given facts about the package audited against its code; unlike a trusted unit, it is the one module touching the package, granting nothing beyond the operation.`),
    ]),
  }),
  aspect("mapped", 1, "A mapped type whose field type depends on its key", "4,374 statements, 38 functions", {
    cases: "written-partial-argument-refused",
    source: ["type G<T, K extends keyof T> = K;", `export function f(x: keyof { z: G<Partial<{ 0: number }>, 0> }): "z" {`, "  return x;", "}"],
    why: "a mapped type {[P in K]: V} gives every key P the same field type V, and TScert reads it only when V does not mention P. Partial, Readonly and Pick write T[P], the type of the source's own field P, so the gate refuses them wherever they are written (tools/type-term.mts:546), even where, as in the case, G discards its argument. In tools/, Readonly over object types meets 37 of the 38 functions and Partial the 38th; Pick meets two of the 37 (measured).",
    todo: "one reading rule more: when the keys are a known list of literal keys, each field k gets V with P replaced by k, T[k] reads the field k of T, and the modifiers ? and readonly apply as written. Readonly&lt;{ a: string }&gt; is then { readonly a: string }. A mapped type over a type parameter with no known keys stays refused. The rule goes with the other type readings in SOURCE-CONTRACTS.md, with a verified case and a refused one (a write through Readonly).",
    trust: "nothing: it is a reading of a type annotation, not a contract.",
  }),
  aspect("api", 4, "A compiler-interface member with no contract", "2,637 statements, 10 functions", {
    cases: "invalid-compiler-api-view-member",
    source: [`import * as ts from "typescript/unstable/ast";`, `import type { Checker } from "typescript/unstable/sync";`,
      "export function base(checker: Checker, n: ts.Node): number {", "  const t = checker.getTypeAtLocation(n);",
      "  return t === undefined ? 0 : checker.getBaseTypes(t).length;", "}"],
    why: "TypeScript's compiler interface is read through views: per class, the list of members TScert has audited (COMPILER-API.md). Checker is that interface's type checker; the case calls its member getBaseTypes, which the list for Checker omits. In tools/ the missing members are mostly type tests of the class Type, isUnionType (10 functions) and isTypeParameter (6, measured), declared isUnionType(): this is UnionType: a true result promises the receiver is a UnionType. TScert reads no promise about a receiver (gap case type-guard-this-refused).",
    todo: "for plain members (getExports and getMembers of the interface's class Symbol, which describes a declared name; and the interface's enum TypePredicateKind), an audit and a listing, as for five members admitted in b2368ec. For the type tests, stated type guards, proposed in COMPILER-API.md and not built: per test, the promise it makes, audited against the bits it tests in the type's numeric field flags, and a rule that narrows the receiver on a true result.",
    trust: `${trust}: each member, and each guard's promise.`,
  }),
  aspect("error", 5, "The options argument of Error", "2,447 statements, 11 functions", {
    cases: "blocker-error-super-options, blocker-error-options",
    source: ["// blocker-error-super-options", "class Failure extends Error { constructor(message: string) { super(message, {}); } }",
      "// blocker-error-options", `export function use(): Error { return new Error("failed", { cause: "reason" }); }`],
    why: "TScert's contract for Error states its message argument alone. Its second argument, an options object, is not stated: by ECMAScript's description of the Error constructor (InstallErrorCause, cited), the host checks whether it has a property cause and, if so, reads it and copies it to the new error; the check and the read may run code (a getter, a proxy). The gate refuses both forms (tools/fragment-classes.mts:754; tools/declaration-graph.mts, “is read with at most 1 argument”).",
    todo: "the contract of new Error(message, options) and super(message, options): options an object whose cause, when present, is copied to the error's own field cause, admitted where the check and the read run no code, such as an object literal of plain fields; the rule goes into SOURCE-ELABORATION.md, “A class extending Error”.",
    trust: `${trust}: the host follows ECMAScript's description of the Error constructor.`,
  }),
  aspect("hash", 6, "Node's createHash", "1,055 statements, 41 functions", {
    cases: "blocker-node-hash-contract",
    source: [`import { createHash } from "node:crypto";`, `export function use(s: string): string { return createHash("sha256").update(s).digest("hex"); }`],
    why: "createHash has no contract, so the gate reads Node's declaration of it and every type that declaration names, each through its written annotations. Its options type HashOptions extends the stream type TransformOptions, where TypeScript gives one member a type it builds itself, with no written declaration behind it; no annotation states that member's type, so the gate refuses. The functions are many and small.",
    todo: "contract entries for createHash and for the update and digest methods of its result (entries for a returned value's methods are a new form), at the arguments tools/ uses (a string algorithm, string or byte data, as Uint8Array or Buffer, the hex encoding; Buffer is aspect 7), after an audit of Node's hash code, which is to establish, among others, what an unknown algorithm and a second digest do. A function with a contract is read through it, and its declaration's types are not read.",
    trust: `${trust}: three entries about Node's crypto module.`,
  }),
  aspect("buffer", 7, "Node's Buffer, reached from node:fs", "681 statements, 58 functions", {
    cases: "blocker-node-buffer-contract",
    source: [`import { statSync } from "node:fs";`, "export function use(path: string): number { return statSync(path).size; }"],
    why: "statSync has no contract (the contracts for node:fs list readFileSync, writeFileSync, existsSync and a few others), so the gate reads its declaration and the types it names. They reach Buffer, whose method Buffer.from returns Buffer&lt;ImplicitArrayBuffer&lt;TArrayBuffer&gt;&gt;: a conditional type over the type parameter TArrayBuffer, which TypeScript computes only once TArrayBuffer is known, so the gate refuses it (tools/computed-types.mts:229). 19 of the functions also read the global Buffer, whose declaring file no contract lists (measured).",
    todo: "contract entries for the node:fs functions tools/ calls, statSync among them, at the arguments it uses, so their declarations are not read; and a contract for the Buffer values tools/ handles, read as the bytes they hold (Uint8Array), with the members it uses.",
    trust: `${trust}: an audited entry for each function and for Buffer.`,
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "The open cases, cheapest trust first", gap: 22,
    body: table(["Step", "Cases", "Trust"], [
      ["Mapped types naming their key (aspect 1)", c("written-partial-argument-refused"), status("ok", "none")],
      ["Checker.getBaseTypes, Symbol's getExports and getMembers, and TypePredicateKind (aspect 4)", c("invalid-compiler-api-view-member"), status("trust", "an audited entry each")],
      ["Error's options (aspect 5)", `${c("blocker-error-super-options")}, ${c("blocker-error-options")}`, status("trust", "ECMAScript's Error")],
      ["Contracts for Node values with methods: createHash, fs, Buffer and Uint8Array (aspects 2, 6, 7)", `${c("blocker-node-hash-contract")}, ${c("blocker-node-buffer-contract")}`, status("trust", "a new entry form")],
      ["Stated type guards, the bulk of aspect 4; a class contract for WeakMap and WeakSet (aspect 2)", `${c("type-guard-this-refused")}, ${c("blocker-weakmap")}`, status("trust", "each guard's promise; a new form")],
    ], [42, 40, 18]) + bullets([
      "The two aspects with no case get one first. Each step turns its gap cases into verified ones; the census, run once on main after a merge, then measures what it moved.",
      "Order (estimated): the reading rule adds no trust; plain entries follow the audits done for compiler-interface members; Error's options are one more stated constructor; new forms of entry come after, and guards and class contracts last.",
    ]),
  }),
];

const deck: Deck = {
  title: "Where TScert's proofs fail",
  slides,
  sections: [
    { description: "Where proofs fail, and the case examples made.", start: "cover" },
    { description: "The cases by priority: closed ones, how and why; open ones, what closing needs.", start: "priority" },
  ],
};
export default deck;
