/* The gap-priorities deep dive: where TScert's proofs of its own code fail,
 * from the diagnostic census, the case examples made for those failures,
 * and the cases by priority, each closed one with how and why it was
 * closed. Built with the deck kit (`make deck NAME=gap-priorities`). */
import { execFileSync } from "node:child_process";
import {
  bullets, card, cards, code, color, cover, point, record, recordSlide, slide, stat, status, table,
  type Deck, type Slide, type Status,
} from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** A case's name, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
const trust = status("trust", "trust change");

/** A cause's slide: its case's code, then why it is refused, what proving
 * it needs and what that would trust, or, for a closed one, how it was
 * closed. */
function cause(id: string, label: string, title: string, o: {
  cases: string; source: string[]; why: string; todo: string; trust: string;
  closed?: { status: string; how: string };
}): Slide {
  const labels = o.closed ? ["Why it was refused", "How it was closed, and why so", "What it trusts"]
    : ["Why it is not proven", "What proving it needs", "What it would trust"];
  return slide(id, {
    label, title, gap: 18,
    note: o.closed ? o.closed.status : `${status("gap", "gap")} ${o.cases}`,
    body: code(o.source) + bullets([point(labels[0] ?? "", o.why), point(labels[1] ?? "", o.closed ? o.closed.how : o.todo), point(labels[2] ?? "", o.trust)]),
  });
}

const prio: [string, string, string, string, string][] = [
  ["1", "Mapped types whose field type is T[P]: Readonly, Pick, Partial", "2,520", "51", `${c("written-partial-argument")}, ${c("blocker-readonly-record")}: ${status("ok", "verified")}`],
  ["2", "Node's Buffer and its byte types", "1,887", "72", c("blocker-node-buffer-contract")],
  ["3", "A key test \"name\" in x", "1,708", "32", c("blocker-in-name-object")],
  ["4", "Node's crypto hash and stream declarations", "1,539", "47", c("blocker-node-hash-contract")],
  ["5", "instanceof of a class another module declares", "1,188", "26", c("blocker-instanceof-imported-class")],
  ["6", "The options argument of Error", "1,134", "14", `${c("blocker-error-super-options")}, ${c("blocker-error-options")}`],
  ["7", "A callback parameter whose context is a library type", "1,045", "16", c("blocker-closure-map-context")],
];

/** The commit that closed the globals and sep cases, as its record states it. */
const closing = record(execFileSync("git", ["log", "-1", "--format=%B", "aa3c69a"], { encoding: "utf8" }), "aa3c69a");

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "Where TScert's proofs of its own code fail, and which cases to close first",
    text: "TScert is run on its own front end (the code that reads TypeScript sources, in the folder tools/), function by function, and most functions are refused. Part 1 finds where the proofs fail, with a census that goes past each function's first refusal, and turns each cause into a small case example. Part 2 ranks those cases by how much code they block, and shows for each closed case how and why it was closed, and for each open one what closing it needs.",
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
    label: "Part 1 · where proofs fail", title: "Two censuses of main at 83cdb42 (2026-10-26)", gap: 22,
    body: cards([
      stat("189 of 499", `functions of tools/ ${status("ok", "verified")} by the census, 1,408 of 12,998 statements (10.8%, measured)`, "ok"),
      stat("394", "functions the diagnostic census takes to their end (below); 42 stop at regions it cannot examine, 62 at the 300 s limit of a stage, 1 at a failure of the compiler interface (measured)"),
      stat("24.3%", "coverage with holes: 3,161 statements outside the regions the diagnostic census had to assume (measured)"),
    ]) + bullets([
      point("The census", "each top-level function of tools/ is copied into a file of its own and run through TScert (make census). A refused function stops at its first reason."),
      point("The diagnostic census", "make census DIAGNOSTIC=1 runs each copy past every refusal: it replaces what it cannot check by an opaque region of assumed type and goes on, so it reports every refusal a function meets. It never reports a function verified."),
      point("Causes", "the refusals of reading the source (the gate, and the planning that lowers it) are grouped by cause and weighted by the statements (an if, a return, an assignment …) of the functions each blocks, and by their number. Refusals of the later stages differ from function to function and are left out. The function lowerFile, 674 statements, meets all seven heaviest causes."),
    ]),
  }),
  slide("cases", {
    label: "Part 1 · from a failure to a case", title: "Each heavy cause has a small case example", gap: 20,
    body: code(["// blocker-in-name-object.ts. Census functions: family-activation.mts#selectionGuard, …",
      "export function nameOf(manifest: unknown): unknown {",
      `  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;`, "}"]) + bullets([
      point("A case example", "is the smallest source with the cause's refusal; one made from the census names in its header the census functions it stands for. The test suite (make suite) checks its expected outcome on every run."),
      point("A gap case", "is a safe program TScert refuses for want of a rule or a contract. A <b>negative case</b> is a refusal that is right: the program could produce a wrong value."),
      point("Which causes get one", `every cause blocking more than 1,000 statements or more than 40 functions: seven causes. Four had gap cases; ${c("blocker-in-name-object")}, ${c("blocker-instanceof-imported-class")} and ${c("blocker-closure-map-context")} are made from this census.`),
      point("Closing a case", "a fix makes it verify, and the census copies of its functions then pass that refusal and stop at the next."),
    ]),
  }),
  slide("priority", {
    label: "Part 2 · cases by priority, diagnostic census at 83cdb42", title: "Seven causes ranked by the code they block: cause 1's cases verified, seven gap cases open", gap: 18,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [4, 44, 12, 10, 30]) + bullets([
      "A cause's statements and functions are those of the functions it blocks at any point: a function blocked by several causes counts under each, so the columns do not add up.",
      `Cause 1's cases verify since this census was taken (slide “Mapped types …”); every other case listed is ${status("gap", "open")}. Closed before this census: node:path's sep and five library globals (slides “Closed: …”); Object.getPrototypeOf is confined to a host boundary (route 5, next slide).`,
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”. The closed cases took route 1; Object.getPrototypeOf took route 5."]),
  }),
  cause("buffer", "Cause 2 · 1,887 statements, 72 functions", "Node's Buffer and its byte types", {
    cases: "blocker-node-buffer-contract",
    source: [`import { statSync } from "node:fs";`, "export function use(path: string): number { return statSync(path).size; }"],
    why: "the node:fs functions with no contract (statSync among them) are read through their declarations, which reach Buffer: Buffer.from returns Buffer&lt;ImplicitArrayBuffer&lt;TArrayBuffer&gt;&gt;, a conditional type over a type parameter, computed only once TArrayBuffer is known, and ArrayBufferLike is an indexed access into a named type. The gate refuses both (measured: 72 functions meet one of them).",
    todo: "contract entries for the node:fs functions tools/ calls, at the arguments it uses, so their declarations are not read; and a contract for the Buffer values tools/ handles, read as the bytes they hold (Uint8Array), with the members it uses.",
    trust: `${trust}: an audited entry for each function and for Buffer.`,
  }),
  cause("in-name", "Cause 3 · 1,708 statements, 32 functions", "A key test \"name\" in x", {
    cases: "blocker-in-name-object",
    source: ["export function nameOf(manifest: unknown): unknown {",
      `  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;`, "}"],
    why: "every function owns a field name, so a test \"name\" in x tells nothing of x's type when x may be a function, and TScert refuses it: 7 such tests in tools/, met 40 times across the 32 functions' copies (measured). Here typeof x === \"object\" has already excluded functions, and the refusal does not use that.",
    todo: "the key test reads the narrowing the condition before it established: a value known to be a non-null object, whose typeof is \"object\", is no function; the rule and its refused counterpart (x possibly a function) go into SOURCE-ELABORATION.md.",
    trust: "nothing: it is a rule of reading the source, with no new assumption.",
  }),
  cause("hash", "Cause 4 · 1,539 statements, 47 functions", "Node's crypto hash and stream declarations", {
    cases: "blocker-node-hash-contract",
    source: [`import { createHash } from "node:crypto";`, `export function use(s: string): string { return createHash("sha256").update(s).digest("hex"); }`],
    why: "createHash has no contract, so the gate reads Node's declaration of it and every type that declaration names. Its options type HashOptions extends the stream type TransformOptions, where TypeScript gives one member a type it builds itself, with no written declaration behind it; no annotation states that member's type, so the gate refuses.",
    todo: "contract entries for createHash and for the update and digest methods of its result, at the arguments tools/ uses (a string algorithm, string or byte data, the hex encoding), after an audit of Node's hash code. A function with a contract is read through it, and its declaration's types are not read.",
    trust: `${trust}: three entries about Node's crypto module.`,
  }),
  cause("instanceof", "Cause 5 · 1,188 statements, 26 functions", "instanceof of a class another module declares", {
    cases: "blocker-instanceof-imported-class",
    source: [`import { IoFailure } from "./blocker-instanceof-imported-class-failure.ts";`,
      "export function wrap(operation: string, run: () => string): string {",
      "  try { return run(); }", "  catch (error) { throw error instanceof IoFailure ? error : new IoFailure(operation); }", "}"],
    why: "x instanceof C narrows x to C's instances, which needs the prototype C's constructor gives them. The gate reads that only for a class declared at the file's top level; the front end tests its own error classes (IoFailure, CompilerFailure …), which other modules declare.",
    todo: "read an imported class's construction and prototype through the import, as a local class's are read, the declaring module being checked on its own; the rule goes with the reading of classes in SOURCE-CONTRACTS.md.",
    trust: "the imported class meets its declaration, as every imported value is read at its declared type.",
  }),
  cause("error", "Cause 6 · 1,134 statements, 14 functions", "The options argument of Error", {
    cases: "blocker-error-super-options, blocker-error-options",
    source: ["// blocker-error-super-options", "class Failure extends Error { constructor(message: string) { super(message, {}); } }",
      "// blocker-error-options", `export function use(): Error { return new Error("failed", { cause: "reason" }); }`],
    why: "TScert's contract for Error states its message argument alone. By ECMAScript's description of the Error constructor (its step InstallErrorCause), the host checks whether the options object has a property cause and, if so, reads it and copies it to the new error; the check and the read may run code (a getter, a proxy).",
    todo: "the contract of new Error(message, options) and super(message, options): options an object whose cause, when present, is copied to the error's own field cause, admitted where the check and the read run no code, such as an object literal of plain fields.",
    trust: `${trust}: the host follows ECMAScript's description of the Error constructor.`,
  }),
  cause("closure-context", "Cause 7 · 1,045 statements, 16 functions", "A callback parameter whose context is a library type", {
    cases: "blocker-closure-map-context",
    source: ["export function bound(scopes: readonly ReadonlySet<string>[], name: string): boolean {",
      "  return scopes.some((scope) => scope.has(name));", "}"],
    why: "an unannotated callback parameter takes the type TypeScript gives it from its context only when that type is built from primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name; a library interface such as ReadonlySet&lt;string&gt;, Map&lt;string, string&gt; or PromiseLike is refused (measured: 16 functions).",
    todo: "read a context type that names a library interface as an annotation naming it would be read, with the same refusals where that reading has none.",
    trust: "nothing new: an annotation of the same type already rests on the same library declarations.",
  }),
  cause("mapped", "Cases verified since the census · cause 1, which blocked 51 functions at 83cdb42", "Mapped types whose field type is T[P], the type of T's field P", {
    cases: "", source: ["// blocker-readonly-record: verified",
      "export function joined(files: Readonly<Record<string, string>>): string {",
      "  let out = \"\";", "  for (const [, text] of Object.entries(files)) out += text;", "  return out;", "}"],
    why: "a mapped type {[P in K]: V} gives every key P the same field type V, and TScert read it only when V does not mention P. Partial, Readonly, Required and Pick write T[P], the type of T's own field P, so the gate refused them wherever they were written. In tools/, Readonly met 45 of the 51 functions, Partial 4 and Pick 3 (measured).",
    todo: "",
    trust: "nothing: it is a reading of a type annotation, not a contract. Still refused, each a stated restriction with its case: T[P] at an interface or alias held by name, a union, an array or a callable; over a written key union; -? over an optional field that may hold undefined, whose meaning depends on the option exactOptionalPropertyTypes.",
    closed: {
      status: `${status("ok", "verified")} blocker-readonly-record, written-partial-argument; mapped-identity, a case of each form`,
      how: "route 1, support: rules mapped-identity and mapped-pick. Over keyof T the type is T's own fields and indexes; over Pick's K, bounded by keyof T, the fields K names. Each marker ? and readonly is added, removed (-) or kept from T, as written. Readonly&lt;Record&lt;string, V&gt;&gt; is the readonly string index. Measured on three census copies: guardClosure now stops at crypto's TransformOptions (cause 4), selectGlobal at keyof over a type parameter; familyTable stops where it did. The effect on the 51 functions is for the next census.",
    },
  }),
  cause("sep", "Closed by aa3c69a · sep, which blocked 29 functions at 963ffa4", "Closed: the constant sep of node:path", {
    cases: "", source: [`import { sep } from "node:path";`, "export function use(path: string): string[] { return path.split(sep); }"],
    why: `Node's declarations make the module one object, whose interface declares readonly sep: "\\\\" | "/". The gate reads an import from a Node module as an annotated constant, function or class, or through a contract, and the contracts listed functions only.`,
    todo: "",
    trust: `${trust}: sep is a data property of the module's object that no code writes, an assumption.`,
    closed: {
      status: `${status("ok", "verified")} blocker-node-path-sep`,
      how: "route 1, support: a contract entry for a module constant, naming the property declaration exactly as reviewed and stating its type, with no parameters and no effect (rule library-module-constant).",
    },
  }),
  cause("globals", "Closed by aa3c69a · globals, which blocked 30 functions at 963ffa4", "Closed: five globals, each an audited contract", {
    cases: "", source: ["// library-math-random: verified",
      "export function rolls(sides: number[]): number[] {", "  return sides.map((n) => Math.ceil(Math.random() * n));", "}"],
    why: "a global of JavaScript's standard library is read only through a contract that lists its exact declaration. Math.random, Object.hasOwn, process.execArgv, process.platform and process.arch had none.",
    todo: "",
    trust: `${trust}: each entry, and that no code writes process.execArgv. WeakMap and WeakSet still need a contract for a class read through its members (${c("blocker-weakmap")}, a gap case).`,
    closed: {
      status: `${status("ok", "verified")} library-math-random, object-has-own, node-process-platform`,
      how: "route 1, support: one audited entry each, no new form. Object.hasOwn converts a string, number or symbol key without running code and writes nothing; Math.random writes nothing a program reaches; process.execArgv is read as process.argv is; platform and arch are strings.",
    },
  }),
  recordSlide("closing-record", closing, ["Trust modified (reviewed overlay of library globals)", "Rule added (library modules: a constant)"]),
  slide("prototype", {
    label: "Library globals · one use in tools/, route 5", title: "Object.getPrototypeOf, confined to a host boundary", gap: 16,
    body: cards([
      card("The use", "The compiler channel (compiler-channel.mts), the front end's link to TypeScript's compiler process, checks and wraps the six methods by which the TypeScript package's private client sends a request, on the client's class prototype."),
      card("Why no other route", "An entry (o) =&gt; object | null is unsound: Array.isArray narrows getPrototypeOf([]) to an array whose writes reach every array; instanceof narrows a prototype to an instance without its fields. No rewrite avoids it: reading a method through the client itself may run a getter, code TScert does not see."),
      card("What it guarantees", "The wrapper sends each request and returns its answer, or a repeated query's earlier one (a stated conjecture). The caller's callback only runs code around that call (send, once): it cannot replace an answer or hide a failure."),
    ]) + code(["// tools/client-prototype.mts: the two functions that read the prototype, refused themselves",
      "export function clientHasMethod(api: API, member: RequestMember): boolean",
      "export function guardClientRequests(api: API, around: (member, receiver, args, send) => void): void"]) + bullets([
      point("How callers verify", `an imported function is read at its stated signature, so the channel is verified against these two (API is the package's class of a compiler process; RequestMember names the six methods); the boundary's own code is reported refused. ${status("ok", "verified")} blocker-client-prototype; ${status("neg", "refused")} blocker-client-prototype-forged, a fake API value.`),
      point("Status", `narrowed, not closed: the channel's functions stop at an earlier refusal, an import of a class whose type parameter has a default, here API (8 functions, below the threshold, measured). ${trust}: the boundary's code, TScert's own and unchecked, meets its two signatures, given facts audited against the TypeScript package's code.`),
    ]),
  }),
  slide("next", {
    label: "Part 2 · order of work", title: "The open cases, least new assumption first", gap: 22,
    body: table(["Step", "Cases", "Trust"], [
      ["Readings with no new assumption: \"name\" in x (cause 3), a library type as callback context (cause 7)", `${c("blocker-in-name-object")}, ${c("blocker-closure-map-context")}`, status("ok", "none")],
      ["Imported classes read through the import (cause 5)", c("blocker-instanceof-imported-class"), status("trust", "the import's declaration")],
      ["Error's options (cause 6)", `${c("blocker-error-super-options")}, ${c("blocker-error-options")}`, status("trust", "ECMAScript's Error")],
      ["Contracts for Node values with methods, a kind of entry no contract has yet: fs and Buffer (cause 2), createHash (cause 4)", `${c("blocker-node-buffer-contract")}, ${c("blocker-node-hash-contract")}`, status("trust", "an audited entry each")],
    ], [46, 36, 18]) + bullets([
      "Each step turns its gap cases into verified ones; the census and the diagnostic census, run once on main after a merge, then measure what it moved.",
      "Estimated cost order, which overrides the ranking by size: readings that add no assumption first; an imported class rests on what imports already rest on; Error's options are one more stated constructor; new forms of entry come last.",
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
