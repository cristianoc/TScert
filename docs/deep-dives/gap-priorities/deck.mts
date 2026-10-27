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
 * closed; a narrowed one says what was closed and what stays open. */
function cause(id: string, label: string, title: string, o: {
  cases: string; source: string[]; why: string; todo: string; trust: string;
  closed?: { status: string; how: string; narrowed?: true };
}): Slide {
  const labels = o.closed?.narrowed ? ["Why it was refused", "What was closed, and what stays open", "What it trusts"]
    : o.closed ? ["Why it was refused", "How it was closed, and why so", "What it trusts"]
    : ["Why it is not proven", "What proving it needs", "What it would trust"];
  return slide(id, {
    label, title, gap: 18,
    note: o.closed ? o.closed.status : `${status("gap", "gap")} ${o.cases}`,
    body: code(o.source) + bullets([point(labels[0] ?? "", o.why), point(labels[1] ?? "", o.closed ? o.closed.how : o.todo), point(labels[2] ?? "", o.trust)]),
  });
}

const prio: [string, string, string, string, string][] = [
  ["1", "Mapped types whose field type is T[P]: Readonly, Pick, Partial", "2,520", "51", `${status("ok", "closed")} ${c("blocker-readonly-record")}, ${c("written-partial-argument")}, ${c("mapped-identity-named")}`],
  ["2", "Node's Buffer and its byte types", "1,887", "72", `${status("gap", "narrowed")} ${c("blocker-node-buffer-contract")}`],
  ["3", "A key test \"name\" in x", "1,708", "32", `${status("gap", "narrowed")} ${c("blocker-in-name-object")}`],
  ["4", "Node's crypto hash and stream declarations", "1,539", "47", `${status("gap", "narrowed")} ${c("blocker-node-hash-contract")}`],
  ["5", "instanceof of a class another module declares", "1,188", "26", `${status("ok", "closed")} ${c("blocker-instanceof-imported-class")}`],
  ["6", "The options argument of Error", "1,134", "14", `${status("gap", "narrowed")} ${c("blocker-error-options")} verified; ${c("blocker-error-options-return")} open`],
  ["7", "A callback parameter whose context is a library type", "1,045", "16", `${status("gap", "open")} ${c("blocker-closure-map-context")}`],
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
    label: "Part 2 · cases by priority, diagnostic census at 83cdb42", title: "Seven causes ranked by the code they block: two closed, four narrowed, one open", gap: 18,
    body: table(["#", "Cause", "Statements", "Functions", "Cases"], prio, [4, 44, 12, 10, 30]) + bullets([
      "A function blocked by several causes counts under each, so the columns do not add up.",
      `Since this census: causes 1 and 5 ${status("ok", "closed")}; causes 2, 3, 4 and 6 ${status("gap", "narrowed")}, meaning part of the cause closed and part still refused. Closed before it, at census 963ffa4: node:path's sep and five globals; Object.getPrototypeOf sits behind a host boundary (route 5). How many functions these fixes gain is not yet measured.`,
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
    ], [22, 78]) + bullets(["Stated in SOURCE-REWRITES.md, “Deciding what a refusal of TScert's code calls for”. The closed and narrowed causes took route 1, with one runtime check (route 2) in files.mts's installed; Object.getPrototypeOf took route 5."]),
  }),
  cause("closure-context", "Cause 7 · 1,045 statements, 16 functions", "A callback parameter whose context is a library type", {
    cases: "blocker-closure-map-context",
    source: ["export function bound(scopes: readonly ReadonlySet<string>[], name: string): boolean {",
      "  return scopes.some((scope) => scope.has(name));", "}"],
    why: "an unannotated callback parameter takes the type TypeScript gives it from its context only when that type is built from primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name; a library interface such as ReadonlySet&lt;string&gt;, Map&lt;string, string&gt; or PromiseLike is refused (measured: 16 functions).",
    todo: "read a context type that names a library interface as an annotation naming it would be read, with the same refusals where that reading has none.",
    trust: "nothing new: an annotation of the same type already rests on the same library declarations.",
  }),
  cause("mapped", "Closed by e93eb63, da191e7 and 64f1871 · cause 1, which blocked 51 functions at 83cdb42", "Closed: mapped types whose field type is T[P], the type of T's field P", {
    cases: "", source: ["// blocker-readonly-record: verified",
      "export function joined(files: Readonly<Record<string, string>>): string {",
      "  let out = \"\";", "  for (const [, text] of Object.entries(files)) out += text;", "  return out;", "}"],
    why: "TScert read a mapped type {[P in K]: V} only where V does not mention P. Partial, Readonly, Required and Pick write T[P], so the gate refused them. In tools/, Readonly met 45 of the 51 functions (measured).",
    todo: "",
    trust: "nothing: it is a reading of a type annotation, not a contract. Still refused, each with its case: T[P] at a union, an array, a callable, a class, a record with a method, or a shape that reaches itself; over a written key union; and Required (removing ?) over an optional field that may hold undefined, whose meaning depends on the compiler option exactOptionalPropertyTypes.",
    closed: {
      status: `${status("ok", "verified")} blocker-readonly-record, written-partial-argument, mapped-identity-named`,
      how: "route 1, support: rules mapped-identity and mapped-pick. Over keyof T the type is T's fields and index signatures; over Pick's K, bounded by keyof T, the fields K names; each marker ? and readonly is added, removed or kept from T, as written. A named interface or alias is read as its fields, bases included. The diagnostic census of the 51 functions at 64f1871 has no mapped-type refusal, against 96 at 83cdb42, and nativeIteratorDefinition, a census function, verifies (measured 2026-10-26).",
    },
  }),
  cause("buffer", "Narrowed by 787002e · cause 2, which blocked 72 functions at 83cdb42", "Node's file system read through audited entries; Buffer still open", {
    cases: "", source: ["// blocker-node-buffer-contract: verified", `import { statSync } from "node:fs";`, "export function use(path: string): number { return statSync(path).size; }"],
    why: "the node:fs functions with no contract (statSync among them) were read through their declarations, which reach Buffer: Buffer.from returns Buffer&lt;ImplicitArrayBuffer&lt;TArrayBuffer&gt;&gt;, a conditional type over a type parameter, and ArrayBufferLike is an indexed access into a named type. The gate refuses both (measured: 72 functions meet one of them).",
    todo: "",
    trust: `${trust}: an entry each for statSync, mkdirSync, chmodSync and writeFileSync, audited against Node 25.2.1's lib/fs.js; a Stats keeps its prototype chain, and isFile, isDirectory and its five other is… methods stay data properties holding functions.`,
    closed: { narrowed: true,
      status: `${status("ok", "verified")} blocker-node-buffer-contract, node-fs-stat`,
      how: "route 1, support: with a contract at the arguments tools/ passes, a function's declaration, which mentions Buffer, is not read. statSync is a constant whose type is an interface of call signatures, read through a new form of entry (a const, with no base but Function). An is… method's result is unknown, since other code may replace a helper it calls, so files.mts's installed compares isFile() to true, a runtime check recorded in SOURCE-REWRITES.md. Open: a function annotated with Buffer is still refused; there is no case of it yet.",
    },
  }),
  cause("in-name", "Narrowed by cc04cef–960767f · cause 3, which blocked 32 functions at 83cdb42", "A key test \"name\" in x: admitted where x cannot be a function", {
    cases: "", source: ["// blocker-in-name-object: a gap, at a later refusal",
      "export function nameOf(manifest: unknown): unknown {",
      `  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;`, "}"],
    why: "every function owns a field name, so a test \"name\" in x tells nothing of x's type when x may be a function, and TScert refused it on every operand: 7 such tests in tools/, which block the 32 functions (measured).",
    todo: "",
    trust: `${trust}, in the caller contract (what TScert assumes of the values a function receives from code it does not check): a value received at a record type reads inherited fields as it would own ones, so an optional field it lacks reads undefined. An error passed at { message?: number } is outside it: there v.message + 1 gives "1" under Node (in-outside-caller-contract).`,
    closed: { narrowed: true,
      status: `${status("ok", "verified")} in-function-key; ${status("gap", "gap")} blocker-in-name-object`,
      how: "route 1, support: k in o for a key a function owns or inherits (name, call, apply …) is admitted where the operand's type, narrowed by the condition before it, holds no function. Open: manifest is typed unknown, which the conditions do not narrow to an object type, so manifest.name cannot be read; that needs a type naming every non-null object.",
    },
  }),
  cause("hash", "Narrowed by 395a66d · cause 4, which blocked 47 functions at 83cdb42", "Node's crypto hash read through one audited entry", {
    cases: "", source: ["// blocker-node-hash-contract: verified", `import { createHash } from "node:crypto";`, `export function use(s: string): string { return createHash("sha256").update(s).digest("hex"); }`],
    why: "createHash had no contract, so the gate read Node's declaration of it and every type that declaration names; HashOptions extends the stream type TransformOptions, where TypeScript infers a member's type with no declaration to check it against.",
    todo: "",
    trust: `${trust}: the entry, audited against Node 25.2.1's hash.js; every Hash keeps Node's prototype, which holds update and digest as data properties.`,
    closed: { narrowed: true,
      status: `${status("ok", "verified")} blocker-node-hash-contract, node-crypto-hash`,
      how: "route 1, support: createHash at \"sha256\", update at a string, digest at \"hex\", each stating no footprint, so it may change any location; another algorithm or encoding is refused. An entry may define named types for its result, so update's result type is the Hash it was called on. Open: update with bytes (a Uint8Array or Buffer), which three files of tools/ pass.",
    },
  }),
  cause("instanceof", "Closed by 0fd783b · cause 5, which blocked 26 functions at 83cdb42", "Closed: instanceof of a class another module declares", {
    cases: "", source: ["// blocker-instanceof-imported-class: verified",
      `import { IoFailure } from "./blocker-instanceof-imported-class-failure.ts";`,
      "export function wrap(operation: string, run: () => string): string {",
      "  try { return run(); }", "  catch (error) { throw error instanceof IoFailure ? error : new IoFailure(operation); }", "}"],
    why: "x instanceof C narrows x to C's instances, which needs the prototype C's constructor gives them. The gate read that only for a class declared at the file's top level; the front end tests its own error classes (IoFailure, CompilerFailure …), which other modules declare.",
    todo: "",
    trust: `${trust}: the imported class's binding holds the class its declaration creates, and the lookup of Symbol.hasInstance along its prototype chain finds only data properties yielding the standard method.`,
    closed: {
      status: `${status("ok", "verified")} blocker-instanceof-imported-class, instanceof-class-value-import`,
      how: "route 1, support: the test a local class gets, for a class TScert checks in another source module, free of TypeScript errors and suppressions, whose base is nothing, Error or another such class. The declaring module may use the class only to construct it, test with it or read a member; passing it on or writing to it, which could replace its prototype or install a hook, is refused. Three later commits refuse eight programs that broke the first version's assumptions (a replaced prototype, a suppressed error, other spellings and aliases, code in export default, extends or a static setter); six are new cases run under Node.",
    },
  }),
  cause("error", "Narrowed by 940af14 and b2d7d97 · cause 6, which blocked 14 functions at 83cdb42", "Error's options argument, cause copied as ECMAScript states", {
    cases: "", source: ["// blocker-error-options: verified", "export function use(reason: unknown): void {", `  throw new Error("failed", { cause: reason });`, "}"],
    why: "TScert's contract for Error stated its message argument alone. By ECMAScript's Error constructor (its step InstallErrorCause), the host checks whether the options object has a property cause and copies it to the new error; the check and the read may run code (a getter, a proxy).",
    todo: "",
    trust: `${trust}: the host's Error constructor follows ECMAScript's description; external code creates no enumerable own cause on an error.`,
    closed: { narrowed: true,
      status: `${status("ok", "verified")} blocker-error-options, blocker-error-super-options, error-options`,
      how: "route 1, support: new Error(m, o), Error(m, o) and super(m, o) at options { readonly cause?: unknown }; the caller contract (slide on \"name\" in x) makes cause a data field there, so the copy runs no code. cause joins message and stack as keys the source may not write on a value that may be an error. Open: returning the Error is refused, since TypeScript's Error declares name and TScert's model of an error holds none (blocker-error-options-return, a gap).",
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
    label: "Part 2 · order of work", title: "What stays open, ordered by the trust each adds, least first", gap: 22,
    body: table(["Step", "Cases", "Trust"], [
      ["1. A type naming every non-null object, which typeof x === \"object\" and x !== null narrow unknown to (cause 3)", c("blocker-in-name-object"), status("ok", "none")],
      ["2. A library type as a callback parameter's context (cause 7)", c("blocker-closure-map-context"), status("ok", "none")],
      ["3. An Error read at TypeScript's type, name included (cause 6, returning the Error)", c("blocker-error-options-return"), status("trust", "Error.prototype's name")],
      ["4. A stated type for Node's Buffer, treated as a Uint8Array, also for update with bytes (causes 2 and 4), a new form of entry", "no case yet", status("trust", "an audited entry each")],
    ], [52, 30, 18]) + bullets([
      "The census and the diagnostic census, run once on main after the merges of e93eb63–960767f, measure what the closed and narrowed causes gained and rank what stays open.",
      "The order is by trust added, which overrides the ranking by size: steps 1 and 2 add none, step 3 one stated property, step 4 a new form of entry.",
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
