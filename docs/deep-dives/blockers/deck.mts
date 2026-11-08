/* The blockers deep dive: what stops TScert's own front end in the census
 * of 963ffa4, the blockers found past the first refusal by rewriting each
 * slice's source, seven of them investigated by hand, the repros and the
 * pipeline cases they became, and the changes to tools/. Built with the
 * deck kit (`make deck NAME=blockers`). */
import {
  bullets, card, cards, code, cover, inline, point, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";

/** Prose: `code` in backticks takes the code colour. */
const t = inline;

/** A blocker investigated by hand: where it is met, who refuses it and why,
 * its repair and what that trusts, and what lies behind it. */
function blocker(id: string, weight: string, title: string, o: { where: string; who: string; repair: string; behind: string }): Slide {
  return slide(id, {
    label: `Blocker · ${weight}`, note: "investigated by hand", title: t(title), gap: 18,
    body: bullets([
      point("Where", t(o.where)), point("Who refuses, and why", o.who),
      point("Repair, and what it trusts", t(o.repair)), point("Behind it", t(o.behind)),
    ]),
  });
}

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · its own front end",
    title: "What stops TScert's own code, and what lies behind it",
    text: "TScert checks type claims about TypeScript programs and is run on its own front end, function by function. In the run of 2026-10-24, 178 of its 490 functions are verified. This deck ranks what stops the other 312, finds blockers hidden behind the first one with crude rewrites of the source, and lists a small reproducing file for each of the 121 blockers found. Seven large blockers are investigated: their cause, the repair, and what the repair would trust. Each blocker's cause is a pipeline case of TScert's suite, and patterns TScert rightly refuses are removed from its own code (slides “45 cases stand for the 121 repros” and “Changes to tools/”).",
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert works, in three cards", gap: 28,
    body: cards([
      card("Verified, refused", `TScert ${status("ok", "verifies")} a function when it proves it safe: every value the function reads, writes or returns has its declared type. Otherwise it ${status("neg", "refuses")} the function, naming the first place it could not prove. A refusal is the location and its reason.`),
      card("The four stages", "A source passes through, in order: the <b>gate</b>, which reads the TypeScript and refuses what lies outside the language TScert admits; the <b>producer</b>, which proposes types for every expression; the <b>search</b>, which looks for a proof of them; and the <b>checker</b>, proved correct in the Lean proof assistant, which checks that proof. Only the gate and the checker are trusted."),
      card("Contract", `TScert's reviewed description of code it does not check itself, such as a Node or TypeScript library function: written and audited by hand. A contract is an assumption the result rests on; adding one widens what TScert trusts.`),
    ]),
  }),
  slide("terms2", {
    label: "Words used in this deck, continued", title: "Slices, the census, and coverage", gap: 28,
    body: cards([
      card("Slice", "One top-level function of TScert's front end (the folder tools/), copied into a file of its own with the definitions of its file it uses, and run alone through TScert. A slice stops at its first refusal: whatever else it would meet stays unseen."),
      card("Census", "The run of every slice: 490 slices, one per function, in the census of commit 963ffa4 (2026-10-24, each stage allowed 300 s)."),
      card("Statement coverage", "The share of the front end's TypeScript statements (an if, a return, an assignment …) that lie inside verified functions: 1,347 of 12,698 in that census, 10.6%."),
    ]),
  }),
  slide("census", {
    label: "Where things stand", title: "178 of 490 functions verify; 312 stop at 104 different first refusals", gap: 26,
    body: cards([
      stat("178 of 490", `functions of tools/ ${status("ok", "verified")} in the census of 963ffa4 (measured)`, "ok"),
      stat("104", "distinct first refusals among the other 312, grouped by their reason (measured by the rewrite loop of the next slides)"),
      stat("10.6%", "statement coverage: 1,347 of 12,698 TypeScript statements inside verified functions (measured)"),
    ]) + bullets([
      "Where the 312 stop (measured): 212 at the gate or the producer, 100 in the search; none in the checker.",
      "Many functions share one blocker: the ten largest each meet between 13 and 56 functions (slide “The ten largest blocker families”).",
      "A slice stops at its first refusal, so fixing a blocker only shows the next one, one census at a time. The next two slides describe how to look further ahead.",
    ]),
  }),
  slide("loop", {
    label: "Looking past the first refusal", note: "crude, may change behaviour, never counted as verified",
    title: "Rewrite the slice's source until it reaches the end", gap: 18,
    body: bullets([
      point("The loop", "run the slice; at a refusal, apply a crude local rewrite of the slice's copy that gets past it; record the refusal as a blocker; run again; stop when the slice reaches the end, when no rule rewrites the refusal, after 12 rewrites, or after 1,200 s."),
      point("A diagnostic only", `it is a separate tool (dev/blocker-rewrites.mts, branch blocker-rewrites, commit 90feee4) that edits copies and changes nothing TScert trusts. A rewritten slice that gets through is reported as “reaches the end after rewrites R1…Rn”, never as ${status("ok", "verified")}.`),
      point("What it may change", "a rewrite can alter what the code does, so a blocker found after it is one the original code may or may not meet. The order says what was exposed, not what caused it."),
    ]) + table(["Rule", "Refusal", "Rewrite (in the slice's copy)"], [
      ["R1", "Readonly over a record (slide “Readonly”)", "the same record with readonly fields written out"],
      ["R2", "node:path's constant `sep`", "a local declared constant of type `string`"],
      ["R3", "`Object.entries` at two kinds of overload", "a local declared function `(o: object) => [string, unknown][]`"],
      ["R4", "an expression the search cannot type", "a hole: a call of a declared function returning the expected written type"],
      ["R5", "an unsupported statement with no result", "an empty statement"],
    ].map(r => r.map(t)), [10, 42, 48]),
  }),
  slide("holes", {
    label: "A second measure", title: "Coverage with holes: 11.3% against 10.6% verified", gap: 24,
    body: cards([
      stat("17", "of the 312 functions reach the end after rewrites: 13 after holes (R4), 3 after Readonly (R1), 1 after sep (R2) (measured)"),
      stat("295", "stop at a refusal none of the five rules rewrites (measured): the catalogue is the loop's limit"),
      stat("11.3%", "coverage with holes: 1,435 of 12,698 statements; 88 more than verified (measured)"),
    ]) + bullets([
      point("Coverage with holes", "the statements of verified functions plus those of functions that reach the end after rewrites, a statement touched by a rewrite counted as not covered."),
      point("The gap", "88 statements, in functions the found blockers stop and whose slices reach the end once those blockers are rewritten. It grows as more slices reach the end."),
      "The 88 are the statements of those 17 functions that no rewrite touched; with a larger catalogue more slices reach the end and the gap grows (estimated).",
    ]),
  }),
  slide("ranking", {
    label: "Ranking, measured by the loop's run", title: "The ten largest blocker families", gap: 14,
    body: table(["Family (groups refusals of one reason)", "Functions", "Statements", "Met first / after rewrites"], [
      ["search: an expression with no proof of its type", "56", "1,187", "55 / 5"],
      ["Readonly over a record", "29", "1,087", "15 / 14"],
      ["node:path's constant `sep`", "27", "701", "27 / 0"],
      ["Node's `Buffer`", "27", "309", "25 / 2"],
      ["a library global no contract covers", "21", "765", "8 / 14"],
      ["a callback parameter TypeScript types as `any`", "21", "654", "0 / 21"],
      ["`Object.entries` at two kinds of overload", "21", "654", "21 / 0"],
      ["compiler-API members outside TScert's reviewed lists", "20", "3,091", "20 / 0"],
      ["the sync API's conditional member type", "17", "119", "14 / 3"],
      ["crypto's hash options", "13", "404", "5 / 8"],
    ].map(r => r.map(t)), [55, 13, 14, 18], { compact: true }) + bullets([
      "Functions: distinct functions whose slice meets the family; statements: those functions' statements. Families overlap, so the columns do not add up.",
      "The last column counts functions meeting the family as their first refusal and after a rewrite; a function can meet it both ways, so the two may add to more than the total. No slice meets the callback parameter typed any first.",
      "The 20 functions of a later slide, “An empty array written into a field”, are among the 56 of the first row.",
    ]),
  }),
  blocker("sep", "27 functions, 701 statements", "node:path's constant `sep`", {
    where: "the slices of tools/family-activation.mts (21), declaration-graph.mts (5) and files.mts (1) read `sep`, a property of the object node:path exports.",
    who: t("the gate. TScert reads a library module's value only through a reviewed entry, and the entries cover functions, not constants: a missing contract, not a restriction any document states (cited: SOURCE-CONTRACTS.md, “Library modules”)."),
    repair: "a constant entry in the reviewed list of library modules, stating `sep` as `\"/\" | \"\\\\\"`. It adds one host assumption: nothing replaces `path.sep` while the program runs; Node lets code write it (observed with a Node script). Size: about 30–50 lines (estimated).",
    behind: "rewriting `sep` by hand in 7 of the 27 slices (a test apart from the loop), 1 reaches the end; the others stop at Node's `Buffer`, crypto's hash options, and an in test (`\"name\" in f`) on a function value (observed).",
  }),
  blocker("buffer", "27 + 13 functions", "Node's `Buffer`, and crypto's hash", {
    where: "most of tools/files.mts: `Buffer.compare` in one sorting helper, the fs functions `statSync`, `mkdirSync` and `chmodSync`, whose path parameter admits a `Buffer`, written `Buffer` and `Dirent` types, and `createHash`.",
    who: t("the gate, rightly: an unlisted Node function is read as its declaration states, and `Buffer`'s declaration is outside what TScert reads (its parent type `Uint8Array` is refused by itself; `Buffer` has about 100 members, some running caller code) (observed and cited)."),
    repair: "new reviewed entries: the fs functions at string paths, `createHash` with `update` and `digest`, and a `Buffer` type with a closed list of the members the code uses. They add host assumptions, statements about Node that TScert does not check: Buffers keep their standard methods, hashing runs no caller code, each to audit against Node's source. Reading files as text instead would change what the hashing computes.",
    behind: "`Dirent`, the `TextDecoder` global, a read of `splice` on a value that may be an array or a record, and Readonly (observed).",
  }),
  blocker("entries", "21 functions, 654 statements", "`Object.entries` at two kinds of overload", {
    where: "every one waits on one helper of tools/type-term.mts, `sameData`, which calls `Object.entries` twice: once on a value narrowed to an array, where TypeScript picks the generic overload, once on an object, where it picks the plain one.",
    who: t("the gate, refusing one member used at a generic and a plain overload. SOURCE-CONTRACTS.md states the refusal (“a generic, optional or modified method … [is] refused”) without saying what behaviour it excludes; its cause is how TScert translates a library member for the checker, from plain signatures or from one generic signature, never both (cited)."),
    repair: "let a member carry both kinds: small, no new trust (estimated).",
    behind: "`sameData` stays refused: its parameters are typed `unknown`, an array fails the generic overload's parameter, the plain overload excludes values made by the compiler, which TScert keeps opaque (a stated restriction), and a callback is typed `any` (observed). Passing it would need stated parameter types, a change to TScert's source under its rules for such changes (estimated).",
  }),
  blocker("syncapi", "17 + 7 functions", "The sync API's `API` class", {
    where: "functions using the class `API` of TypeScript's synchronous compiler interface (the sync API), through which TScert's front end asks TypeScript about a program. It is declared `class API<FromLSP extends boolean = false>`: 17 functions use it as a type (14 of them meet this first), 7 in compiler-channel.mts import it as a value.",
    who: t("the gate, twice. (a) TScert reads a conditional type (`X extends Y ? A : B`) only once its type parameters are known, and its reviewed list of the class's members states `updateSnapshot` with the parameter type `FromLSP extends true ? … : …`, read for the class in general, never at `API<false>`: no program can use `API` as a type, a defect of the reviewed list (observed: even a function only calling `api.close()` is ") +
      status("neg", "refused") + t("). (b) TScert does not admit constructing `API` (`new API(…)`), a stated restriction, and refuses a value import of it even where the code only uses it as a type (cited)."),
    repair: "(a) read such a class at each use, with its type parameters known, as TScert already reads a type alias holding a conditional type: no new trust (estimated). (b) read a value import as a value only where the code constructs it: 5 of the 7 then meet (a) (estimated).",
    behind: "`Object.getPrototypeOf` outside the reviewed globals, members outside the reviewed views, and `Parameters<API[\"updateSnapshot\"]>` (observed in part).",
  }),
  blocker("hoisting", "20 functions of fragment-statements.mts", "An empty array written into a field", {
    where: "the write `gate.hoisted = []` in the function `hoisting`, which every one of these slices includes (`gate` here names the parser's state object, not the stage).",
    who: t("the search refuses, rightly; the cause is a defect of the producer. The producer proposes the new array `[]` by itself, as an array of nothing, instead of at the field's type `Stmt[]` (a write to a local variable already gets the expected type, a write to a field does not), and the search finds no proof: an array's elements are a cell other references may share, so an array of nothing is no `Stmt[]` (cited: the write rule in Lean)."),
    repair: "pass the field's type to the written value, for field and index writes: about 5–10 lines of the producer, no Lean change, no new trust, since every write is still checked (estimated).",
    behind: "the same cause at `gate.hoist = {…}` one line up; then, in `forInStmt`, a call `gate.local(d.name)` after a narrowing, cause not established (observed).",
  }),
  blocker("views", "20 functions, 3,091 statements", "Compiler-API members outside the reviewed views", {
    where: "reads of 7 members of TypeScript's compiler API that TScert's reviewed list for each class (a view) leaves out: `Type.isUnionType` (10 functions), `Checker.getContextualType` (4), `API.parseConfigFile` (2) and four others.",
    who: t("the gate, rightly: a member outside its view is a located refusal until it is reviewed (cited: COMPILER-API.md, reading rule 4). Five are omissions, four of them members the front end began to read after the views were written; the two this-is-X guards, such as `isUnionType(): this is UnionType`, are left out on purpose."),
    repair: "the five: one reviewed entry each, its implementation audited. The guards used only as a test: read without their promise, no new trust. Using what the guard promises, as computed-types.mts does with `getTypes()` after `isUnionType`, needs stated type guards, a large design already listed in TScert's status file.",
    behind: "the next members outside the views (`isTypeParameter`, `Snapshot.dispose`, `isStringLiteralType`) (observed).",
  }),
  blocker("readonly", "29 functions, 1,087 statements", "Readonly over a record", {
    where: "`Readonly<Record<K, V>>` in tools/array-prototype.mts and guard-closure.mts, reached by their importers. `Readonly<T>` is the mapped type `{ readonly [P in keyof T]: T[P] }`.",
    who: t("the gate's reader of types, which reads a mapped type's value once and so refuses a value naming its key, as `T[P]` names `P`. SOURCE-CONTRACTS.md states the refusal but no behaviour it excludes (cited); that it is a limit of the reader only is estimated."),
    repair: "read such a mapped type key by key, each field taking `T`'s member type: in the trusted gate, no new contract, about 50–120 lines with a formal rule (estimated). The same rule reads `Pick` over known keys.",
    behind: "rewriting Readonly by hand in 13 of the slices (a test apart from the loop), 3 reach the end; the others stop at `import.meta`, a local class extending `Error`, the sync API's conditional type, `Object.hasOwn` and one search refusal (observed).",
  }),
  slide("kinds", {
    label: "The seven, side by side", title: "Three are defects or omissions; the rest need contracts or a rule", gap: 18,
    body: table(["Blocker", "Kind", "Repair", "Trust it adds"], [
      [t("empty array into a field"), `${status("neg", "defect")} of the producer`, t("the field's type passed to the value"), status("ok", "none")],
      [t("`API` class as a type"), `${status("neg", "defect")} of a reviewed list`, t("read per use, at its arguments"), status("ok", "none")],
      [t("5 compiler-API members"), "omission", t("a reviewed entry each"), status("trust", "5 audited members")],
      [t("Readonly over a record"), "limit of the reader (estimated)", t("a mapped type read key by key"), `${status("ok", "none")} (trusted gate)`],
      [t("`Object.entries`"), "limit of the translation", t("a member of both kinds"), `${status("ok", "none")}; the helper stays refused`],
      [t("`sep`"), "missing contract", t("a constant entry"), status("trust", "path.sep is not replaced")],
      [t("`Buffer`, `createHash`"), "missing contracts", t("reviewed entries"), status("trust", "host assumptions to audit")],
    ], [27, 22, 30, 21]) + bullets([
      "Every repair is estimated, not built. Behind each, the hand rewrites found more blockers: lifting one rarely lets a slice reach the end by itself (observed: sep 1 of 7, Readonly 3 of 13).",
    ]),
  }),
  slide("repros", {
    label: "Repros", note: "repros/annotated-pattern-007.ts", title: "121 small files, one per blocker found", gap: 20,
    body: cards([
      stat("121", "repro files, each showing its refusal through TScert (measured: all 121 reproduce)"),
      stat("94 / 17 / 10", "found only as a first refusal / only after rewrites / both (measured)"),
      stat("21 lines", "median length after the header; the longest is 188 (measured)"),
    ]) + bullets([
      "Each file states the refusal, the original locations it stands for, the functions it blocks and the command reproducing it; by stage: 58 in the search, 46 at the gate, 17 in the producer.",
      "They are listed, not made to pass: each is a test of the language TScert admits (its “fragment”, the word gate refusals use), small enough to work on alone.",
    ]) + code([
      "/* Refusal: gate: an annotated pattern is outside the fragment (line 549, col 13)",
      "   Functions blocked: 8 · Seen: first (header abridged) */",
      "export function use(p: [number]): number {",
      "  const [x]: [number] = p;",
      "  return x;",
      "}",
    ]),
  }),
  slide("cases", {
    label: "The repros as pipeline cases", title: "45 cases stand for the 121 repros", gap: 22,
    body: cards([
      stat("45", t("cases `blocker-*.ts` in pipeline/examples, one per cause; 67 repros merge into them and existing cases already cover the other 54 (measured)")),
      stat("42 / 3", `${status("gap", "gaps")}: safe programs TScert should verify / ${status("neg", "negatives")}: refusals that are themselves the point (measured)`),
      stat("212", "named gaps in the whole suite, 170 before these; 2,188 of 2,188 cases as expected (measured, commit c6d1b65)"),
    ]) + bullets([
      t("**A case** is a source with its expected outcome: the suite checks each blocker is still refused exactly so, and reports it when a fix makes it verify or moves its refusal. Run them alone with `make cases P=blocker-`."),
      point("Gap or negative", "a refusal blocked by a missing rule or contract is a gap; a negative only where the refused behaviour is a principled restriction or an unsafe program."),
      t("**A negative in TScert's own code** cannot stay: a pattern rightly refused in a small file is rightly refused in tools/ too. So each negative's pattern was removed from tools/ wherever it occurs (next slide)."),
    ]),
  }),
  slide("tools", {
    label: "Changes to tools/", title: "Three patterns refused on principle, removed from TScert's own code", gap: 10,
    body: table(["Pattern refused", "Why refusing it is right", "The change in tools/ (commit c6d1b65)"], [
      ["`\"guards\" in promise` selects an arm of a union whose other arm may carry extra properties",
        "the other arm may own the field at another type: `blocker-in-field-narrowing` returns `undefined` from a function typed `number`",
        "each arm states the other's field absent (`guards?: never`) and readers test the value: `guardOf` and 15 other functions"],
      ["a check of readonly JSON data promising writable fields",
        "a check shows what the fields hold now, not what may be written: promised writable fields, a caller could write any value of the field's type into an object another reference expects to hold a narrower one",
        "the footprint, effect and guard-promise fields are readonly: `isClosedFootprint`, `isCallEffect`"],
      ["a callback whose parameter TypeScript types as `any` (`Object.entries` on an object)",
        "`any` gives TScert no type to check the parameter's uses against",
        "the entry is annotated `[string, unknown]`: `sameData`, `mergeRefusal`"],
    ].map(r => r.map(t)), [30, 33, 37]) + bullets([
      t("Also: four readers of an import clause read `phaseModifier` instead of `isTypeOnly`, a field the compiler API's declarations leave out (cited: SOURCE-REWRITES.md); for ordinary and type imports the two give the same answer."),
      "Each change keeps what the code computes, and docs/SOURCE-REWRITES.md states the property the code lacked, the rewrite and the functions; make suite and make test pass (measured).",
      t("Census effect, on the 48 slices of the changed functions and their users (measured, 2026-10-25): 0 verified before and after; some move to a later refusal (`guardOf`), others stop before the repaired code (the type-term.mts slices, at `Object.entries`)."),
    ]),
  }),
  slide("next", {
    label: "Limits, and the next round", title: "The catalogue of rewrites decides how far the loop sees", gap: 24,
    body: bullets([
      point("What the loop cannot see", "the obligations inside what a rewrite removed (64 original statements in this run, measured), and refusals with no rule: a refusal where branches meet, or about what memory holds, has no local rewrite."),
      point("Where it stops", "295 of 312 functions at a refusal no rule rewrites (measured). Each new rule lets the loop look past one more kind, and adds the repros it then finds."),
      point("The next phase", t("grow the catalogue and rerun, turning every new blocker into a case; the gap cases are worked on one at a time with `make cases P=blocker-`, and the census measures the effect from time to time.")),
      point("Conjecture", "coverage with holes grows faster than verified coverage as rules are added, and the families that most often appear after rewrites gain weight in the ranking: library globals, Readonly and crypto; the most frequent, the callback parameter typed any (21 functions), is a pattern removed from tools/ (slide “Changes to tools/”)."),
    ]),
  }),
];

const deck: Deck = {
  title: "What stops TScert's own code",
  slides,
  sections: [
    { description: "Terms, and where the census stands.", start: "cover" },
    { description: "The rewrite loop, coverage with holes and the ranking.", start: "loop" },
    { description: "Seven blockers investigated.", start: "sep" },
    { description: "Repros, the cases they became, the changes to tools/, and the next round.", start: "repros" },
  ],
};
export default deck;
