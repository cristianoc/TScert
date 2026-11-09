/* The method-effects deep dive: what a stated method effect (`Modifies<P, T>`)
 * is, where it can be written and how far it reaches, with examples that
 * verify and examples refused, and its use on TScert's own parser with the
 * outcomes measured. Built with the deck kit
 * (`node dev/deck-cli.mts method-effects`). */
import {
  bullets, card, cards, code, color, columns, cover, inline, panel, para, point, rules, slide, stat, status, table,
  type Deck, type Slide,
} from "../../../dev/deck.mts";
import { SYNTAX } from "../../../dev/style-tokens.mts";

/** Prose with `code` in backticks, as the kit's `inline` reads it. */
const t = inline;
/** A test case's name, in the code colour. */
const c = (name: string): string => color(SYNTAX.t, name);
/** A paragraph led by a bold phrase, its own punctuation included. */
const lead = (title: string, html: string): string => `<b>${title}</b> ${html}`;
const verified = status("ok", "verified"), refused = status("neg", "refused"), gap = status("gap", "gap");

const slides: Slide[] = [
  cover("cover", {
    label: "TScert · method effects in practice",
    title: "Using method effects: examples and outcomes",
    text: t("TScert checks type claims about TypeScript programs: it verifies a function when it proves the function safe, and otherwise refuses it (next slides). A function can state what it may change, and TScert checks the statement against the function’s body. Statements are certified (next slides) on test cases and on 61 functions of TScert’s own parser for TypeScript (“What expr’s statement rests on”). Of 16 parser functions measured, 11 verify (census of 2026-10-24): 9 verify in the census before the statements too, and 2 verify relative to statements that are audited, not certified, among them that of `expr`, the parser’s expression parser, at one call of Array `map` (“pattern’s map relies on the expression parser’s statement”; what it takes and what to expect follow there). The 16 are described on “More terms, for TScert’s own source”."),
  }),
  slide("terms", {
    label: "Words used in this deck", title: "How TScert works, in three cards", gap: 28,
    body: cards([
      card("Verified, refused", "TScert verifies a function when it proves it safe: every value the function reads, writes or returns has its declared type. Otherwise it refuses the function, naming the first place it could not prove."),
      card("Statement", "An effect is what a call may change; in this deck a statement is an effect a function declares in its result type (“What you write”), bounded by a footprint (“The footprint F”). A statement of TypeScript code, such as an if, is called a TypeScript statement."),
      card("Producer and checker", "TScert’s parser, its front end, reads the TypeScript source; it is trusted, and reviewed by hand. From the parser’s output an untrusted producer proposes type claims (the types it asserts each value has) and effects, also of code that states none, and an untrusted search looks for their proofs. Untrusted: their mistakes cannot make TScert accept, since a checker, written and proved in Lean, a proof assistant, accepts only what it checks."),
    ]),
  }),
  slide("terms2", {
    label: "Words used in this deck, continued", title: "Three more cards", gap: 28,
    body: cards([
      card("Certified, relative", "A statement is certified when the checker has checked the function’s own body against it, in a run that verifies (a run: TScert checking one source file, or a slice, “More terms, for TScert’s own source”; it verifies when every function in it does). A function that relies on a statement not certified is verified relative to it: proved assuming the statement holds."),
      card("Contract", t("TScert’s description of a built-in or library function, such as Array’s `map` or a method of TypeScript’s compiler API: reviewed by hand, and in parts proved in Lean (which parts: “Built-ins state footprints in their contracts”) against the steps the ECMAScript specification gives the function (lean/Verification/Semantics/FootprintNatives.lean).")),
      card("Test case", `A source file of TScert’s test suite with its expected outcome, ${verified} or ${refused}, such as ${c("method-effect-map.ts")}. A refused test case passes when TScert refuses it with the expected diagnostic.`),
    ]),
  }),
  slide("problem", {
    label: "The problem it solves", note: `code adapted from test cases ${c("method-effect-map.ts")} and ${c("invalid-map-method-call-effect.ts")} · ${refused}`,
    title: t("If map’s callback calls a method known only by its type, the result may have holes"),
    body: columns([
      code(["// Log: a class with a method", "// note(n: number): number", "function notes(log: Log,", "    xs: number[]): number[] {",
        "  const r: number[] =", "    xs.map((x) => log.note(x));", "  return r;", "}"]),
      para(lead("Holes.", t("TScert reads `number[]` as: every index below the array’s length reads a number. A missing index, a hole, reads `undefined`, so an array with holes is no `number[]` to TScert (TypeScript’s own `number[]` admits one). `xs` is a `number[]`, so it starts with no holes.")), 24) +
      para(lead("map and its callback.", t("`map` reads the array’s length once, then visits each index, skipping one that is missing and leaving a hole there in its result. A callback that removes elements of `xs` during the walk (`pop`, `shift`, setting `length` smaller) makes later indices missing; `log.note` could, if `log` holds a reference to `xs`.")), 24) +
      para(lead("What TScert cannot see.", t("For a call of a non-generic function declaration of the same module that no code reassigns, TScert finds the effect from that function’s code. `log.note(x)` is a method call, and its code depends on the value: `log` may be any value of type `Log`, an instance of a subclass that overrides `note` or another object of the same shape. So TScert assumes the worst: `map`’s result may have holes, and the function is refused at the assignment to `r`.")), 24) +
      para(lead("The answer.", t("The effect is written once, on the method’s declaration, and checked there; every value the program introduces at the type is checked against it, an overriding method where its subclass is declared and any other object where it is passed as a `Log`; a value from outside code, such as an input of a checked function, is assumed to meet it.")), 24),
    ], [36, 64]),
  }),
  slide("write", {
    label: "What you write", note: `from test case ${c("method-effect-map.ts")} · ${verified}`,
    title: t("The effect goes in the result type, as `Modifies<P, T>`"),
    body: code([`note(n: number): Modifies<{ values: "any"; stores: "grow" }, number> {`, "  this.entries.push(n);", "  return n + 1;", "}"]) + bullets([
      t("`Modifies` needs no import, only its declaration file listed in the project’s tsconfig.json: it is a global type alias in tools/resolvable.d.ts (tools/, the directory of TScert’s TypeScript front end). To TypeScript, `Modifies<P, T>` is just `T`, so the code compiles and runs unchanged. TScert recognises `Modifies` by that declaration, or an identical copy of its file: another type called `Modifies` is an ordinary type."),
      t("To TScert it is a statement about the call: on a normal return, the call changes memory that existed before it at most as P, the frame, allows. With `onThrow: true` in P, this holds also when the call throws; without it, the statement says nothing about a throw."),
      t("P has the class keys `values` (written value below) and `stores` (store), whose settings the next slide lists, an omitted key keep, and optionally `onThrow: true`; in prose this deck writes the settings without quotes. `note` states store: grow (it keeps arrays’ hole-free prefixes hole-free, next slide, as its `push` onto `entries`, a `number[]` field of its class `Log`, three slides on, does) and value: any, because `push`’s contract states value: any (two slides on)."),
      t("TScert checks the function’s own body against the statement in a run that includes its definition, whether or not any code calls it; the statement is certified when that run verifies. Callers rely on the statement."),
    ]),
  }),
  slide("footprint", {
    label: "The footprint F", title: "Two dials: ordinary locations and arrays", gap: 22,
    body: para("In TScert’s model an array is a <b>store</b>, the list of its element locations, and each element is a location holding a value. store bounds changes to stores: which indices hold an element. value bounds changes to every other location, the <b>ordinary</b> ones: object fields, variables, and the contents of array elements. Each dial orders its settings keep, then grow (store only), then any; one footprint is within another when each of its dials allows no more. Memory the call allocates itself is always free to change.", 24) +
      rules(["value:  keep ⊑ any        store:  keep ⊑ grow ⊑ any"]) +
      table(["Setting", "Allows, on memory that existed before the call", "For example"], [
        ["value: keep", "no change to ordinary locations", "—"],
        ["value: any", "any change to ordinary locations", "writing a field or a captured variable"],
        ["store: keep", "no change to any store", "—"],
        ["store: grow", t("every hole-free prefix of an array (indices 0 to k−1, all holding elements) stays hole-free; `unshift` moves elements, which rewrites their contents and so also needs value: any"), t("`push`, `unshift`")],
        ["store: any", "any change to stores", t("`pop`, `shift`, shortening `length`, `reverse` (on an array the call did not allocate; on one with holes, `reverse` moves them)")],
      ], [24, 46, 30]),
  }),
  slide("natives", {
    label: "The footprint F, continued", title: "Built-ins state footprints in their contracts", gap: 30,
    body: bullets([
      t("`push`’s contract is value: any, store: grow. store: grow is proved in Lean from `push`’s steps in the ECMAScript specification (theorem Arr.push_grow, lean/Verification/Semantics/FootprintNatives.lean). The part reviewed by hand says that `push` changes nothing but its array’s store and its elements’ contents. It allows changes to the contents of elements that existed before the call, which are ordinary locations, so it states value: any; by the ECMAScript steps, `push` itself writes only indices past the old length, and TScert states no tighter contract for it."),
      t("`map`’s contract has five signatures: four for a hole-free array and a callback within one of the footprints (value, store) {keep, keep}, {any, keep}, {keep, grow} or {any, grow}, each with a hole-free result, proved (map_rely, FootprintNatives.lean) assuming `map` tests presence only between callbacks (reviewed by hand), since `map` reads the length once and grow keeps the indices below it, and each giving the whole `map` call the callback’s footprint, so a caller keeps what that footprint preserves; and one for any array and callback, whose result may have holes (a callback with store: any may remove elements). Any of the four that the callback’s footprint is within gives a hole-free result; that footprint is found from the callback’s code and its callees’ statements and contracts."),
      `value: any, store: any is ${refused} as a statement: it states nothing.`,
    ], 26),
  }),
  slide("map", {
    label: "Example that verifies", note: `abridged from test case ${c("method-effect-map.ts")} · ${verified}`, gap: 32,
    title: t("A method that only appends keeps map’s result hole-free"),
    body: columns([
      code(["export class Log {", "  entries: number[] = [];", "  note(n: number): Modifies<", `    { values: "any"; stores: "grow" }, number> {`,
        "    this.entries.push(n);", "    return n + 1;", "  }", "}", "export function notes(log: Log,", "    xs: number[]): number[] {",
        "  const r: number[] = xs.map((x) => log.note(x));", "  return r;", "}"]),
      para(point("Checked at the method", "its body only pushes onto a field, which is within value: any, store: grow.")) +
      para(point("Used at the call", t("the callback calls a method stating store: grow, so TScert uses one of `map`’s hole-free signatures, and the assignment to `r` verifies. If `log` is an instance of a subclass the program declares, that subclass’s `note` is checked against the same statement."))) +
      para(lead("Without a statement", `such a call is ${refused}: test case ${c("invalid-map-method-call-effect.ts")} has a class whose method states no effect, called the same way.`)),
    ]),
  }),
  slide("refused", {
    label: "Examples refused", note: `abridged from the test cases named · ${refused}`, gap: 16,
    title: "Three statements that fail their check",
    body: panel("", para(`<b>A body that breaks its statement.</b> ${t("`bump` states that nothing changes, but pops the array it is given")} (${c("invalid-method-effect-method.ts")}).`, 24) +
        code([`class Bump { bump(xs: number[], x: number): Modifies<{}, number> {`, "  xs.pop(); return x; } }"])) +
      panel("", para(`<b>An unstated call inside.</b> ${t("`run` states that nothing changes and calls `this.helper`. Though `helper` changes nothing, a `Runner` may hold there any function of the field’s type, which states no effect")} (“Contract closure”, later; ${c("invalid-method-effect-unstated-dependency.ts")}).`, 24) +
        code(["function helper(xs: number[], x: number): number { return x; }", "class Runner { helper: typeof helper = helper;",
          `  run(xs: number[], x: number): Modifies<{}, number> {`, "    return this.helper(xs, x); } }"])) +
      panel("", para(`<b>An override.</b> ${t("`Drain.take` overrides `Base.take` and pops; the override need not repeat `Modifies`: its body is checked against `Base.take`’s statement")} (${c("invalid-method-effect-override.ts")}).`, 24) +
        code([`class Base { take(xs: number[], x: number): Modifies<{}, number> { return x; } }`,
          "class Drain extends Base { take(xs: number[], x: number): number { xs.pop(); return x; } }"])),
  }),
  slide("limits", {
    label: "Refused forms", note: "the main ones; docs/SOURCE-FRAGMENT.md lists the rest", gap: 16,
    title: "Forms that cannot carry a statement",
    body: table([status("neg", "Refused"), "Why"], [
      ["async functions", "the body may run on after an await, once the call has returned, and a throw in it rejects the returned Promise instead of leaving the call, so no statement covers the body"],
      ["overloaded functions", "the body is checked once, at one signature, so a statement on one overload would not cover the others"],
      ["generic arrows, function expressions and methods, any method of a generic class", "each is checked at bounds (upper types) the producer chooses for its type parameters, which may not cover every type argument a caller uses"],
      ["constructors and construct signatures", "the effect of constructing an object belongs to its class’s whole construction (field initialisers and constructor body), so no constructor carries a statement"],
      ["declaration files and packages", "their code lies outside the checked program, and no run of TScert checks it"],
      ["getters and setters", "TScert refuses every accessor definition, with or without a statement"],
      [t("`Modifies` as the type of a parameter, a field or an array element itself (`x: Modifies<…>`)"), "a statement is the effect of the signature whose result it is"],
      ["F given as a named type alias", t("TScert reads F only from the literal written inside `Modifies`")],
    ], [30, 70]) + para(`A generic function declaration may carry a statement: its annotated parameters are its inputs, so it is certified over its whole written signature. Its callers ignore the statement, so a ${t("`map`")} callback calling one gets ${t("`map`")}’s signature with holes: the generic declaration’s instances carry no footprint at that call.`, 24),
  }),
  slide("forms", {
    label: "Where you can write it", note: "abridged; exclusions on “Forms that cannot carry a statement”", gap: 26,
    title: "At the result of a signature: methods, interfaces, function types",
    body: panel(`An interface member · ${c("method-effect-interface.ts")} ${verified}`,
      code([`interface Limit { over(n: number): Modifies<{}, boolean>; }`,
        "function firstOver(limit: Limit, xs: number[]): number { return xs.findIndex((x) => limit.over(x)); }"]) +
      para(t("Each object passed where a `Limit` is expected is checked against the statement there. `findIndex` visits every index, reading a hole as `undefined`; with a callback that changes nothing, as here, the hole-free `xs` stays hole-free and each `x` is a number; without the statement `x` could be `undefined`, which `over` does not accept."), 24)) +
      panel(`A function type, here a parameter’s · ${c("method-effect-callback-parameter.ts")} ${verified}`,
        code([`function mapped(xs: number[], f: (x: number) => Modifies<{}, number>): number[] {`,
          "  const r: number[] = xs.map((x) => f(x)); return r; }"]) +
        para(`${t("`map`’s result is hole-free; an arrow passed as `f` is checked against `f`’s statement where it is passed: one that pops `xs` is")} ${refused} (${c("invalid-method-effect-callback-argument.ts")}).`, 24)),
  }),
  slide("forms2", {
    label: "Where you can write it, continued", note: `adapted from ${c("method-effect-field.ts")}, ${c("method-effect-onthrow.ts")} · ${verified}`, gap: 20,
    title: "A field holding a module function, and a throw as an exit",
    body: panel("A field holding a module function",
      code([`function scaled(this: Scale, n: number): Modifies<{}, number> {`, "  return n * this.factor; }",
        "class Scale { factor: number = 2; scaled: typeof scaled = scaled; }"]) +
      para(t("A module function is a top-level function of a module; `this: Scale` is TypeScript’s this-parameter. The field’s type is the function’s own, statement included, so a call `s.scaled(x)`, for `s: Scale`, relies on it; a function written into the field is checked against that type. (`Runner`’s `helper` field, on “Examples refused”, has the type of a function stating nothing.) TScert’s own parser holds many functions this way (later slides)."), 24)) +
      panel("A throw as a possible exit",
        code([`positive(n: number): Modifies<{ onThrow: true }, number> {`, `  if (n < 0) throw new Error("negative"); return n; }`,
          "// c: Check, the class of positive; xs: number[]",
          "const r: number[] = xs.map((x) => { try { return c.positive(x); } catch { return 0; } });"]) +
        para(`${t("The callback returns normally from its catch block, so what `positive` changes when it throws counts toward the callback’s return: with `onThrow`, nothing, and `map`’s result is hole-free. Without `onThrow` the throw is unbounded")} (${refused} variant: ${c("invalid-method-effect-stated-throw-caught.ts")}).`, 24)),
  }),
  slide("rules", {
    label: "Two rules that decide how far it reaches", tone: "code", gap: 30,
    title: "A statement holds everywhere and depends on its callees",
    body: columns([
      panel("Over the whole domain", para("The statement must hold for every receiver and argument the signature admits. An arrow’s or function expression’s statement is proved once, at a signature admitting every argument its annotation admits, so it does not depend on what a call site passes; a generic one is refused (“Forms that cannot carry a statement”).", 24)),
      panel("Contract closure", para("A call through a method, field or parameter counts at the statement its type carries, since such a value may hold any function; one stating nothing defeats the statement. A stated function’s callees must be one of:", 24) +
        bullets([
          "a method, field or parameter stating an effect within it;",
          "a non-generic function declaration of the same module that no code reassigns (TScert finds its effect from its code), or an imported function stating an effect within it;",
          "a built-in whose contract states a footprint within it;",
          t("for a statement without `onThrow`, a function whose result type is `never` (no normal return to bound);"),
          "a function defined in the body, whose own calls meet the same rule.",
        ]) + para(t("A `try`/`catch` in a stated body may catch a call’s throw only if the callee states `onThrow`."), 24)),
    ], [2, 3]) + para(t("TScert’s parser makes many of its calls through `Gate`’s fields (next slides), so stating an effect on one of its functions means stating it on everything it reaches that way."), 25),
  }),
  slide("owncode", {
    label: "Using it on TScert’s own code", title: "More terms, for TScert’s own source", gap: 20,
    body: cards([
      card("Slice and census", t("A slice is one top-level function of tools/ (TScert’s TypeScript front end) plus the definitions of its own file it uses, run alone through TScert; definitions of other files, such as `Gate`’s class, are read at their declared types. It stops at the first place TScert refuses. The census runs every slice: 488 slices, one per function of tools/, in the census run at commit 38ed032 (2026-10-24); the census at commit 6a3a864 (466 slices) predates the statements.")),
      card("Gate", t("The class holding the state of TScert’s parser for TypeScript. Besides its data fields, its methods are of two kinds: its own, such as `span`, and fields holding module functions of other files, such as `expr` and `pattern` (later slides), called as `gate.expr(…)`.")),
      card("The 16 measured", "16 functions of three parser files (fragment-statements.mts, fragment-expressions.mts, fragment-classes.mts): the 11 that the design document (docs/drafts/method-effects.md) names for measuring, and 5 others that WORK.md, the project’s status file, records. Each runs as a slice; the stages lowering (the parsed program to TScert’s calculus, the core language its checker reasons about), producer, search, checker and explanation (the stage that locates and explains a refusal) each may take 300 s before it counts as a timeout."),
    ]) + para(`The 16: ${c("enumMembers, enumOpen, resolve, moduleFunction, inertRead, collect, inert, patternDefaults, steppedPattern, pattern, forOfPattern")} (these 11 ${status("ok", "verify")}); ${c("protocolPattern, patternStmt, neverAssigned")} (stopping later, “What to expect”), ${c("abrupt")} (${refused} inside the function ${c("markEarly")}, census of 38ed032); ${c("classBody")}.`, 24),
  }),
  slide("tscert", {
    label: "Using it on TScert’s own code", title: "Statements around Gate", gap: 14,
    body: table(["Definition", "Statement", "Status"], [
      [t("Module functions in `Gate`’s fields: `patternDefaults` (collects the default expressions of a destructuring pattern), `inert` (whether an expression runs only its own code and writes only locals)"), "value keep, store keep", status("ok", "certified, in their own slices")],
      [t("Same kind: `steppedPattern` (makes the parser reject an array pattern whose parts may run code between iterator steps; it writes a captured variable)"), "value any, store keep", status("ok", "certified, in its slice")],
      [t("What `expr` (the expression parser) reaches through `Gate`’s fields and methods and by direct call: 157 of the 167 functions an untrusted scan finds, `expr` and `pattern` among them; the other 10 state less"), "value any, store grow", status("ok", "certified where their slice verifies, pattern among them; not expr, whose slice is refused (“What expr’s statement rests on”)")],
      [t("`Gate`’s own methods: `span` (a node’s position), `local` (the parser’s name for a binding), `hasTypeParam` (whether a type parameter is in scope)"), "value keep, store keep", status("gap", "stated, not certified")],
      [t("`Gate`’s own method: `typeParamName` (the name a type parameter has in the parser’s output; its body uses for-of over an array, whose step’s contract states value: any)"), "value any, store keep", status("gap", "stated, not certified")],
    ], [52, 17, 31], { compact: true }) + bullets([
      t("`Gate`’s own methods are not certified: no slice that includes `Gate`’s class verifies (40ab4d7’s commit message), and `span`’s body calls `node.getStart`, which needs the checker rule on “What expr’s statement rests on”. A slice of another file reads `Gate` at its declared type, so it relies on these statements without checking them."),
      t("`getText`, `getStart` and eight other methods of `Node` and `SourceFile`, listed in TScert’s contract for the compiler API, have a contract stating value: keep, store: keep, also on a throw (`onThrow: true`)."),
    ]),
  }),
  slide("closure", {
    label: "The line that needs expr’s statement", note: "abridged from tools/fragment-statements.mts", gap: 24,
    title: "pattern’s map relies on the expression parser’s statement",
    body: code(["const props: PatternPropAst[] = node.elements.filter((el) => !el.dotDotDotToken).map((el) => {",
      "  … return { …, target: gate.pattern(el.name, names),", "    default_: el.initializer ? gate.expr(el.initializer) : null };", "});"]) + bullets([
      point("What it is", t("`pattern` parses a destructuring pattern, such as `{ a, b = f() }`. For an object pattern it maps the elements other than a rest `...r` (whose `dotDotDotToken` is set) to a `PatternPropAst` each, the parsed form of one property. `filter`’s callback calls nothing. The `map`’s callback (besides `gate.fail`, typed `never`, and `ts.isIdentifier`, not shown), whose `default_` is the property’s default expression parsed, calls `gate.pattern` (`pattern` itself, on the element’s name; `names` collects the names bound so far) and `gate.expr`, the expression parser, on its default: both module functions in `Gate`’s fields, so the calls rely on the statements the fields’ types carry (“A field holding a module function”).")),
      point("Reach", t("in the census run at commit 6a3a864, before the statements, 21 slices stop first at this `map`: `pattern`’s, `forOfPattern`’s (the parser of a pattern in `for (const { a } of xs)`), and 19 others whose slice includes `pattern`. With the statements, `pattern`’s and `forOfPattern`’s slices verify (census slices at 300 s, 2026-10-24), and the other 19 stop at other places (“What to expect”).")),
      point("Cost", t("to keep the `map`’s result hole-free, `pattern` and `expr` state an effect, and so does what they reach through `Gate`’s fields and methods. `pattern` calls itself through the field `gate.pattern`, whose type carries `pattern`’s own statement: the call relies on it by the rule for calls through a field (“A field holding a module function”), which is not circular, since the function written into the field is checked against its type there. By contract closure, `expr`’s statement holds only if everything it reaches does: 157 of the 167 functions an untrusted syntactic scan finds state value: any, store: grow (“Statements around Gate”).")),
    ]),
  }),
  slide("needed", {
    label: "What expr’s statement needs", note: "D-numbers: decisions of the design document", gap: 18,
    title: "What expr’s statement rests on",
    body: bullets([
      lead("forEachChild,", t("TypeScript’s method calling a visitor function on each child of a syntax node, which functions `expr` reaches call: its contract has one signature per footprint of the table on “The footprint F” (six: value keep or any, with store keep, grow or any), taking visitors within that footprint and making the call within it, as `map`’s does (“Built-ins state footprints in their contracts”) (design decision D7; that it runs no code of the program but its visitors is reviewed by hand).")),
      lead("TypeScript’s type checker.", t("The parser reads type annotations through a scope, an object of type `TermScope` whose function members resolve names and types and state value: any, store: grow. TScert’s reader of declaration files (.d.ts files) makes such scopes, which query TypeScript’s own type checker, distinct from TScert’s checker. Those queries are read as an audited contract, reviewed by hand: value: any, store: grow on normal return, except six that may receive an object of the program: sending it to TypeScript’s process converts it to JSON, which runs its `toJSON` method and getters, so these six state no effect, and a body calling one has no certified bound on its effect (design decision D8 (a)).")),
      lead("The shift calls.", t("`shift` on an array the call did not allocate allows any change to stores. By design decision D5, an exception to the rule that TScert’s source is not rewritten to fit the verifier (approved 2026-10-23, WORK.md), `Gate`’s four shifts on its two stacks of scopes (in `enterTypeParams` and `leaveTypeParams`) are field writes, such as `this.typeParamScopes = this.typeParamScopes.slice(1)`, unobservable since no other code holds either array; the two in closures of `protocolForOf` (the parser of for-of over an iterable) are reads at counters.")),
      lead("A checker rule", t("for a method call with names or literals as arguments on a value of several shapes, such as `node.getStart(file)` on a `Node`: TScert reads and calls the method in one step, which no rule bounding a footprint admits, so a body making it has no certified bound on its effect (design document §10). `Gate`’s own methods make such calls (`span` calls `node.getStart`). The design document adds the rule if a measured slice is refused at such a call.")),
      lead("Statements", t("on everything `expr` reaches, each certified where a verifying slice includes it, callers otherwise verified relative to it: 61 of the 183 functions `expr` and the parser’s `TermScope` reach are certified (docs/drafts/method-effects-inventory.md, 2026-10-24).")),
    ]),
  }),
  slide("outcomes", {
    label: "Outcomes measured, 2026-10-24", gap: 16,
    title: "11 of the 16 measured parser functions verify, 2 relative to statements not certified",
    body: columns([
      stat("45", `test cases of method effects (merge 72917dd): 14 ${verified}, 30 ${refused}, 1 ${gap} (the generic declaration on “Forms that cannot carry a statement”); in the suite run on the working tree of commit 7714666 (2026-10-24), each of the 2,138 test cases gets its expected outcome`),
      stat("11 of 16", `measured parser functions ${status("ok", "verify")} (census of 38ed032, 300 s): 9 also before the statements (census of 6a3a864), and ${c("pattern")} and ${c("forOfPattern")}, relative to the statements of ${c("expr")} and Gate’s own methods. 4 of the other 5 stop after pattern’s map (“What to expect”); ${c("classBody")} is ${refused} earlier, for another reason`),
      stat("61 of 183", `functions that ${c("expr")} and the parser’s ${c("TermScope")} reach are ${status("ok", "certified")}, each in its own census slice; the others’ statements rest on an audit of their bodies (docs/drafts/method-effects-inventory.md, 300 s, 2026-10-24)`),
    ]) + bullets([
      t("Under Node, 13 of the 30 refused test cases run (tests/node-runs.mts) and show the refused behaviour: in 11, `map`’s result has a hole; in 2, a parameter default such as `x: number = xs.pop() ?? 0`, on a function stating that nothing changes, pops the array it reads."),
      t("Lost with the statements: `enumMembersTerm` and `enumIntrinsic`. Of 84 census slices around the stated code, 76 verify at 6a3a864, 78 at 762eaea and 76 at fea595c, a later commit of the same work. `enumMembersTerm`, called by a `TermScope` member, states value: any, store: grow and sorts an array a `filter` call has just returned; its slice does not establish the statement at that sort (WORK.md)."),
    ]),
  }),
  slide("next", {
    label: "What to expect", title: "18 parser functions share their next refusal", gap: 24,
    body: bullets([
      point("Measured", t("verified functions of tools/, 175 of 488 in the census run at commit 38ed032, 170 of 466 at 6a3a864; the two commits differ by the statements and by other changes (a guard rule, front-end sharing, two producer fixes; 0e159b5’s commit message), so the difference is not the statements’ alone. In census slices of the functions the statements touch, `pattern` and `forOfPattern` gained, `enumMembersTerm` and `enumIntrinsic` lost (“Outcomes measured, 2026-10-24”).")),
      lead("The other 19", t("(functions of fragment-statements.mts) that stop at `pattern`’s `map` in the census of 6a3a864, at most +19. Census slices of 18 of them, `protocolPattern`, `patternStmt` and `neverAssigned` among them, on commit d2dcda2 (300 s): each gets past the places where the census of 38ed032 refused them (inside the functions `markEarly` and `protocolPattern`) and is refused where TScert derives no type for the write `gate.hoisted = []` in the function `hoisting` (WORK.md).")),
      point("Relative gains", "a gain that relies on the statements of Gate’s own methods is verified relative to them."),
      point("Conjecture", t("coverage by TypeScript statements (those inside verified functions: 1,341 of 12,725 in the census of 38ed032, 10.5%) would rise most with these 19, which include the parser’s large handlers for TypeScript statements (`forStmt`, `switchStmt`, `tryStmt` …).")),
      point("Conjecture, from this case", "a statement is cheap on a leaf, a function whose calls through fields and parameters all have statements or contracts, and expensive on a hub, a function calling much of the program, whose statement depends on everything it reaches."),
    ], 25),
  }),
];

const deck: Deck = {
  title: "Using method effects",
  slides,
  sections: [
    { description: "The problem and what you write.", start: "cover" },
    { description: "Examples that verify and examples refused; where a statement can be written, and the rules on how far it reaches.", start: "map" },
    { description: "Using it on TScert itself: what expr’s statement needs, outcomes measured 2026-10-24, and what to expect.", start: "owncode" },
  ],
};
export default deck;
