#!/usr/bin/env node
/*
 * Trusted front end for the verification experiment (see DESIGN.md).
 *
 * Reads a .ts file and emits a tree of the fragment language (fragment.mts) as
 * JSON, with every node carrying its [start, end) offsets in UTF-16 code units.
 * This program is the SYNTACTIC GATE: a construct outside the fragment is an
 * error, so a program it rejects can never be certified. Anything it accepts,
 * it describes exactly.
 *
 * This program is TRUSTED. It defines what the source text means; the verifier
 * never sees the producer's own parse. The fragment it accepts is stated in
 * ../AGENTS.md and, as a grammar, in the pull request description.
 */
import { API } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type {
  ArrowFunction,
  ClassDeclaration,
  BinaryExpression,
  Expression,
  FunctionDeclaration,
  FunctionExpression,
  Identifier,
  ImportDeclaration,
  InterfaceDeclaration,
  MethodDeclaration,
  Node,
  ParameterDeclaration,
  SourceFile,
  Statement,
  TypeAliasDeclaration,
  TypeParameterDeclaration,
  VariableStatement,
  TypeNode,
} from "typescript/unstable/ast";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import type { DeclarationIdentity, PropertyKey, TypeTerm } from "./declaration-types.mts";
import { bigintText, CLASS_ACCESS, numericLexeme, GENERIC_METHOD_RECEIVER, classMemberRefusal, computedAlias, computedForm, numericKey, optionalTerm, resolutionSlots, restPositions, restRefusal, restTerm, REST_PACK_BOUND, REST_PACK_VALUE, signature, substitute, typeTerm, visitType,
  type TermScope } from "./type-term.mts";
import type {
  Ast,
  BindingAst,
  Expr,
  FunctionAst,
  PatternAst,
  PatternElemAst,
  PatternPropAst,
  Stmt,
  TypeParamAst,
  ArithOp,
  BinaryOp,
  UnaryOp,
  ArrayElemAst,
  TypeofShape,
} from "./fragment.mts";
import { CHAIN } from "./fragment.mts";

/** A value typed `Promise<T>` is assumed to be a built-in promise, which is
 * never fulfilled with a thenable (PROGRAM-TYPING.md, "Async functions and await"):
 * so the source builds no object with a `then`, which could pass for one. */
const FORGED_PROMISE = "an object the source builds with a `then` member could pass for a promise, and a value typed `Promise` is assumed to be a built-in promise";
import type { Span } from "./span.mts";
/** An expression inside its parentheses. */
const skipParentheses = (e: Node): Node => ts.isParenthesizedExpression(e) ? skipParentheses(e.expression) : e;
// thrown.mts reads what the TypeScript API throws into the message the gate reports, without asserting its type.
import { messageOf } from "./thrown.mts";
// syntax.mts reads the name, modifiers and other children a member or declaration of unasked kind carries, checking each is a node.
import { childOf, childrenOf, isStatic, nameOf } from "./syntax.mts";
import { enclosingBinders } from "./computed-types.mts";
// declaration-graph.mts collects the declarations the source reaches: the declaration document the Fragment carries for Lean to lower.
import { collectDeclarations, DeclarationError, libraryArguments, libraryTerm, tsconfigOf, type LibraryType,
  type SeenDiagnostic }
  from "./declaration-graph.mts";
import { asyncCompleteName, asyncReturnName, awaitName, elementAtName, enumIntrinsicName, enumMembersTerm, forInName,
  hasPropertyName, iterateForInName, iterateName, literalTerm, numberText } from "./intrinsics.mts";

/** Why a generator is refused: its body stops at each `yield` and resumes
 * where it stopped when `next` is called again, and no term of the calculus
 * suspends in the middle of code. A generator is a state machine over its
 * suspension points, as TypeScript's downlevel emit writes it; that lowering
 * is not written. */
const GENERATOR = "a generator function is outside the fragment: its body suspends at each `yield` and resumes there on the next call of `next`, which no term of the calculus expresses (the path is a state-machine lowering, as TypeScript's downlevel emit writes one)";

/** The offsets of a statement at which no node of it starts, that lie in no
 * function nested in it (whose statements have their own), from its start up
 * to the next token after it: where a lowering of the statement states the
 * entries of the statements it adds (`sites`), and where the claim reader
 * finds them. */
function freeOffsets(within: Node, file: ts.SourceFile): number[] {
  const start = within.getStart(file);
  const text = file.text;
  let to = within.end;
  while (to < text.length && /\s/.test(text[to] ?? "")) to++;
  const starts = new Set<number>();
  const nested: Span[] = [];
  const visit = (n: Node): void => {
    starts.add(n.getStart(file));
    if (n !== within && (ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n))) {
      nested.push([n.getStart(file), n.end]);
      return;
    }
    n.forEachChild(visit);
  };
  visit(within);
  const free: number[] = [];
  for (let o = start + 1; o < to; o++)
    if (!starts.has(o) && !nested.some(([a, b]) => a <= o && o < b)) free.push(o);
  return free;
}

/** The span of an `if`'s closing parenthesis: the first character past its
 * condition that is neither white space nor a comment. */
function conditionParen(node: ts.IfStatement, file: ts.SourceFile): Span {
  const text = file.text;
  let i = node.expression.end;
  for (;;) {
    if (/\s/.test(text[i] ?? "")) i++;
    else if (text.startsWith("//", i)) i = text.indexOf("\n", i) < 0 ? text.length : text.indexOf("\n", i);
    else if (text.startsWith("/*", i)) i = text.indexOf("*/", i) + 2;
    else break;
  }
  return [i, i + 1];
}

/** Why an iterable whose iterator's type states no `return` is refused where
 * the protocol may close it: leaving the loop early, or a throw out of its
 * body, calls the iterator's `return` if it has one, and an open record type
 * says nothing of that property, which may hold any function. */
const UNCLOSABLE = "an iterable whose iterator's type states no `return` is outside the fragment here: a loop left early, or a throw out of its body, calls the iterator's `return` if it owns one (IteratorClose), and the iterator's open record type says nothing of what that property holds";
/** Why a spread of a program's iterable elsewhere is refused: collecting it
 * runs the iterator's code, which the lowering runs before the statement the
 * spread is in, and that is its place only where nothing the statement
 * evaluates before the spread can be changed by it. */
const SPREAD_POSITION = "a spread of a program's iterable is outside the fragment here: its iterator's code runs where the spread is, which the lowering places before the statement, and that is only its place for the one element of an array literal, or an argument of a call of a name after names and literals nothing assigns, as a statement's value";

/** A question-mark parameter requires an optional suffix. A default may
 * precede a required parameter: callers supply undefined in that position. */
/** The binding a class's static member is: a name no source binding can
 * spell, apart from the instance methods' `C.m`. */
const staticName = (cls: string, member: string): string => `static ${cls}.${member}`;

/** Why an instance member reads none of its class's private static fields. */
const INSTANCE_STATIC = "an instance member or constructor reading a private static field of its own class is outside the fragment: it is a binding the class defines after its methods and constructor, whose closures cannot hold it";
/** Why a static initializer reads its class only through its static fields. */
const STATIC_INIT_CLASS = "a static initializer or static block reading its class other than through an earlier static field is outside the fragment: JavaScript runs it on a class value whose later static fields are undefined, where the model allocates the class value holding them after every initializer";
/** Why a closure a static initializer creates reads no static of its class. */
const STATIC_INIT_CLOSURE = "a closure created by a static initializer or static block reading a static field of its class is outside the fragment: it may run after the field changes, and the class value does not exist yet where it is created";

/** Whether class `cls`, declared at the file's top level, declares a static
 * field named `name` by a property name: an own data property of its class
 * value. */
function staticFieldOf(file: SourceFile, cls: string, name: string): boolean {
  return file.statements.some((s) => ts.isClassDeclaration(s) && s.name?.text === cls &&
    s.members.some((m) => ts.isPropertyDeclaration(m) && ts.isIdentifier(m.name) && m.name.text === name &&
      !!m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword)));
}

/** Whether a node runs code of the program when evaluated: a call, a
 * construction, an iteration, a tagged template, an `await` or `yield`;
 * `except` names constructions that count as running none. A closure it
 * creates runs nothing until called. */
function runsCode(node: Node, except: (n: ts.NewExpression) => boolean = () => false): boolean {
  const visit = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return false;
    if (ts.isNewExpression(n) && except(n)) return (n.arguments ?? []).some(visit);
    if (ts.isCallExpression(n) || ts.isNewExpression(n) || ts.isTaggedTemplateExpression(n) ||
        ts.isAwaitExpression(n) || ts.isYieldExpression(n) || ts.isForOfStatement(n) || ts.isSpreadElement(n) ||
        ts.isArrayBindingPattern(n) || ts.isTemplateExpression(n) || ts.isClassDeclaration(n) ||
        ts.isClassExpression(n)) return true;
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(node);
}

/** Whether a class's static initializers may construct it before its class
 * value exists: constructing it runs no code (no base class, a constructor
 * and instance field initializers running none), and its static
 * initializers and blocks run none but those constructions, so no code of
 * the class, which reads the class value, runs before the class value is
 * bound. */
function selfConstructs(declaration: ClassDeclaration): boolean {
  if (declaration.heritageClauses?.some((h) => h.token === ts.SyntaxKind.ExtendsKeyword)) return false;
  const cls = declaration.name?.text;
  const own = (n: ts.NewExpression) => ts.isIdentifier(n.expression) && n.expression.text === cls;
  // Constructing reads no static field either: one not yet initialized
  // holds nothing in JavaScript, which reads `undefined` there.
  const mentions = (n: Node): boolean => (ts.isIdentifier(n) && n.text === cls) ||
    !!n.forEachChild((c) => mentions(c) || undefined);
  return declaration.members.every((m) => {
    const isStaticMember = isStatic(m);
    if (ts.isConstructorDeclaration(m))
      return !m.parameters.some((p) => p.initializer && (runsCode(p.initializer) || mentions(p.initializer))) &&
        !(m.body && (runsCode(m.body) || mentions(m.body)));
    if (ts.isPropertyDeclaration(m))
      return !m.initializer || (isStaticMember ? !runsCode(m.initializer, own)
        : !runsCode(m.initializer) && !mentions(m.initializer));
    if (ts.isClassStaticBlockDeclaration(m)) return !runsCode(m.body, own);
    return true;
  });
}

/** The static method of class `cls`, declared at the file's top level, named
 * `name` (a property name or a private name's text). */
function staticMethodOf(file: SourceFile, cls: string, name: string): ts.MethodDeclaration | undefined {
  for (const s of file.statements)
    if (ts.isClassDeclaration(s) && s.name?.text === cls)
      for (const m of s.members)
        if (ts.isMethodDeclaration(m) && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) &&
            m.name.text === name && m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword))
          return m;
  return undefined;
}


/** Why a class with a private name takes no part in inheritance. */
const PRIVATE_INHERITANCE = "a class with a private name `#x` in inheritance is outside the fragment: a derived instance's base part is copied, and a copy holds no private slot";

/** The static member name of a class's `[Symbol.hasInstance]` method. */
const HAS_INSTANCE = "[Symbol.hasInstance]";

/** The binding holding a class's prototype object: a name no source binding
 * can spell, apart from an instance method's `C.m` and a static member's. */
const prototypeName = (cls: string): string => `${cls}.[[prototype]]`;

/** The key a class's prototype object owns and no other object does, which
 * `x instanceof C` looks for along `x`'s prototype chain: a name no source
 * key can spell (Lean's `Fragment.reservedSourceKey`). */
const classKey = (cls: string): string => `[[${cls}.prototype]]`;

/** A class as a class extending it reads it: its constructor's parameters,
 * its methods (each the binding holding its closure, its base's included,
 * its own overriding them), and the binding holding its constructor at the
 * fresh instance it allocates. */
type ClassRecord = { params: { name: string; type: TypeTerm }[]; methods: Map<string, string>; fresh: string;
  proto: string | null; binders: string[] };

/** The binding holding a class's constructor where a class extends it: the
 * class value itself, claimed also at the fresh instance it allocates, whose
 * own keys are exactly known. */
const freshName = (cls: string): string => `${cls}.[[class]]`;

/** The class's own binding of its name, which its instance methods, its
 * constructor and its instance field initializers read: JavaScript's class
 * scope binding, initialized before anything in the class body can run. A
 * name no source binding can spell; the initialization unit reads it as the
 * module value the class is (PROGRAM-TYPING.md, "Classes"). */
const selfName = (cls: string): string => `${cls}.[[self]]`;

/** The binding holding a derived instance's base part. */
const baseName = (cls: string): string => `${cls}.[[base]]`;

/** A part of an object literal: a named field, or a spread of a value. */
type ObjectPart = { name: PropertyKey; e: Expr } | { spread: Expr };

/** The hidden name a parameter written as a pattern or with a default
 * binds: a name no source binding can spell. The body's first statements
 * bind the source's names from it, in parameter order (`functionAst`). */
const parameterName = (index: number): string => `parameter ${index}`;

/** Why a class member not named by a plain identifier is refused: each form
 * of name, by what it would mean. */
function unnamedMember(member: ts.ClassElement, isStatic: boolean): string {
  const name = nameOf(member);
  if (name && ts.isPrivateIdentifier(name))
    return "a `#private` member is outside the fragment: it is a private slot of the instance, not a property, and the heap model has no such slot";
  if (name && ts.isComputedPropertyName(name)) {
    const key = name.expression;
    if (isStatic && ts.isPropertyAccessExpression(key) && ts.isIdentifier(key.expression) &&
        key.expression.text === "Symbol" && ts.isIdentifier(key.name) && key.name.text === "hasInstance")
      return "a static `[Symbol.hasInstance]` method is outside the fragment: it replaces the prototype-chain test that `instanceof` is in the model with a call";
    return isStatic
      ? "a static member with a computed key is outside the fragment: a static member is a binding named by its plain name"
      : "a class member with a computed key is outside the fragment: a method is a binding, and its prototype key, named by its plain name";
  }
  if (!name) return "a class member outside the fragment";
  return isStatic ? "a static member needs a plain name" : "a class member needs a plain name";
}

/** The names an expression reads, closures' included: a superset of what
 * it may read when it runs. */
function namesRead(e: unknown, out: Set<string> = new Set()): Set<string> {
  if (Array.isArray(e)) for (const x of e) namesRead(x, out);
  else if (e !== null && typeof e === "object") {
    if ("k" in e && e.k === "id" && "name" in e && typeof e.name === "string") out.add(e.name);
    for (const v of Object.values(e)) namesRead(v, out);
  }
  return out;
}

/** The names a pattern binds, in the order it binds them. */
function patternNames(t: PatternAst): string[] {
  switch (t.k) {
    case "name": return [t.name];
    case "object": return [...t.props.flatMap((q) => patternNames(q.target)),
      ...(t.rest ? patternNames(t.rest.target) : [])];
    case "array": return [...t.elems.flatMap((q) => patternNames(q.target)),
      ...(t.rest ? patternNames(t.rest.target) : [])];
  }
}

/** The label of the block a `switch` is lowered to: a name no source can
 * spell. */
const switchLabel = (node: ts.SwitchStatement, file: SourceFile): string => `%switch@${node.getStart(file)}%`;

/** The statement a `break` leaves or a `continue` repeats: the nearest
 * enclosing loop, or for a `break` also `switch`, not crossing into another
 * function. */
function jumpTarget(node: ts.BreakStatement | ts.ContinueStatement): Node | undefined {
  for (let parent = node.parent; parent && !ts.isFunctionLikeDeclaration(parent); parent = parent.parent)
    if (ts.isWhileStatement(parent) || ts.isForStatement(parent) || ts.isForOfStatement(parent) ||
        ts.isForInStatement(parent) || (ts.isBreakStatement(node) && ts.isSwitchStatement(parent)))
      return parent;
  return undefined;
}

/** Whether a statement list can complete normally, rather than always
 * ending in a jump, a `return` or a `throw` (Lean's `abrupt`, negated). */
function completes(ss: Stmt[]): boolean {
  const last = ss.at(-1);
  if (!last) return true;
  switch (last.k) {
    case "return": case "throw": case "break": case "continue": return false;
    case "if": return last.else_ === null || completes(last.then) || completes(last.else_);
    case "block": return last.label !== null || completes(last.body);
    case "try":
      if (last.finalizer !== null && !completes(last.finalizer)) return false;
      return completes(last.body) || (last.handler !== null && completes(last.handler.body));
    default: return true;
  }
}

function firstOptional(
  parameters: readonly { questionToken?: unknown; initializer?: unknown }[],
): number {
  const i = parameters.findIndex((p) => !!p.questionToken);
  return i < 0 ? parameters.length : i;
}

/* --------------------------------------------------------- the compiler -- */
// The compiler runs out of process and is addressed through one API instance.
// Opening it costs more than reading any one file, so a process that parses
// several shares it, and a process that parses one still pays it once.

let compiler: API | null = null;

// The text this process is working with, per absolute path. The compiler runs
// in another process with its own view of the disk, and a tool that holds a
// source in memory — an annotated rendering, or a fixture it
// just wrote — needs the tree to be the tree of *that* text, not of whatever
// the disk happens to hold. An entry here is what the compiler reads; a path
// with no entry falls through to the real file.
const contents = new Map<string, string>();
const opened = new Set<string>();

/**
 * The project that owns a file: whichever `tsconfig.json` above it claims it,
 * or an inferred one. Exported because a checker-side consumer of this parse
 * needs the same project (and the same compiler process) the gate used.
 */
function projectFor(absolute: string) {
  compiler ??= new API({
    cwd: dirname(absolute),
    fs: {
      readFile: (name) => contents.get(name),
      fileExists: (name) => (contents.has(name) ? true : undefined),
    },
  });
  // A file the compiler already holds is re-read rather than reused: the text
  // for a path can change between two opens in one process, and reusing the
  // first tree would leave every span pointing into a file that is no longer
  // there.
  const changed = opened.has(absolute);
  // The compiler keeps an open file's old text even when `fileChanges` names
  // it. Release that open document first, then reopen it from our current
  // snapshot bytes; otherwise a changed source can receive a stale tree.
  if (changed)
    compiler.updateSnapshot({ closeFiles: [absolute], fileChanges: { changed: [absolute] } });
  const snapshot = compiler.updateSnapshot({
    openFiles: [absolute],
    ...(changed ? { fileChanges: { changed: [absolute] } } : {}),
  });
  opened.add(absolute);
  const project = snapshot.getDefaultProjectForFile(absolute);
  if (!project) throw new Error(`the compiler did not open ${absolute}`);
  return project;
}

/**
 * The compiler's tree for `text`, read as the file at `absolute`. The path
 * decides which `tsconfig.json` governs the file and what a diagnostic names;
 * the text is what is actually parsed.
 */
export function openText(absolute: string, text: string): SourceFile {
  contents.set(absolute, text);
  const file = projectFor(absolute).program.getSourceFile(absolute);
  if (!file) throw new Error(`the compiler produced no tree for ${absolute}`);
  return file;
}

function openFile(absolute: string, text: string): SourceFile {
  contents.set(absolute, text);
  const project = projectFor(absolute);
  const syntax = project.program.getSyntacticDiagnostics(absolute);
  if (syntax.length > 0)
    throw new Error(`gate: parse error: ${syntax[0].text}`);
  const file = project.program.getSourceFile(absolute);
  if (!file)
    throw new Error(`gate: the compiler produced no tree for ${absolute}`);
  return file;
}

/** Release the compiler. A long-lived caller may parse again afterwards. */
export function close(): void {
  compiler?.close();
  compiler = null;
  opened.clear();
  contents.clear();
}

/* -------------------------------------------------------------- the gate -- */
// One parse owns one source file. `fail` and `span` are the only two things
// that need it, and they are the only two that should: a gate rejection names
// a place in the file it is reading.

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators, bigint) is outside it.

class Gate {
  // Written out rather than a parameter property: node strips types, it does
  // not compile them, so the syntax has to be erasable.
  private readonly file: SourceFile;
  /* Type-parameter names are resolved lexically. Keeping frames, rather than
   * one file-wide set, makes nested quantified callables representable without
   * conflating an inner binder with an outer binder of the same spelling. */
  private readonly typeParamScopes: Map<string, string>[] = [];
  private readonly resolutionScopes: TypeParamAst[][] = [];
  readonly resolutionAliases = new Map<string, TypeAliasDeclaration>();
  standardAwaited = false;
  /** The file names the verifier's `Resolvable` (`resolvable.d.ts`). */
  standardResolvable = false;
  /** The file names the verifier's `Awaitable` (`resolvable.d.ts`). */
  standardAwaitable = false;
  private qualificationHeader = false;
  /** Local spelling to the arity and identity of its declaration root. A
   * reference names the declaration TypeScript resolved the spelling to. */
  /** The equations of the declared aliases that name an array, a tuple or
   * another alias, over their parameters: what a rest parameter typed by one
   * collects into (`restType`, `restTerm`). */
  private readonly aliasEquations = new Map<string, { total: number; declaration: DeclarationIdentity;
    expression: TypeTerm }>();
  private readonly declaredTypes = new Map<string,
    { required: number; total: number; declaration: DeclarationIdentity }>();
  /** Global spellings TypeScript binds to a standard library type read at
   * its meaning, `Array<T>` as `T[]` (`LibraryType`). */
  readonly libraryTypes = new Map<string, LibraryType>();
  /* Whether the code being read is strict, by a module or a "use strict"
   * directive (ECMAScript's, not TypeScript's `strict` option). An ordinary
   * function records it: its receiver rule is the strict one. */
  strict = false;
  /** `e[k]` keys TypeScript binds to a `unique symbol` constant, by span:
   * the symbol, as the declaration document lists it. */
  symbolKeys = new Map<string, number>();
  /** The symbols the declaration document lists, by index: which one a
   * computed class member's key names. */
  symbolIdentities: readonly { module: string; name: string }[] = [];
  /** Private names `#x`, by span: the symbol of the member each names, as
   * the declaration document lists it. */
  readonly privateKeys = new Map<string, number>();
  /** The computed types of the file's annotations (`computedForm`), by span:
   * the term TypeScript's evaluation denotes, or the reason it has none
   * (`computed-types.mts`). */
  readonly computedTypes = new Map<string, TypeTerm | { refused: string }>();
  /** The computed keys of the file's annotations' type literals, by span of
   * the key expression: the `unique symbol` each names, as the declaration
   * document lists it, or the reason it names none. */
  readonly symbolNames = new Map<string, number | { refused: string }>();
  /** Mapped types' keys and library mapped types' arguments in the file's
   * annotations, by span: the union of literals and primitives TypeScript
   * computes for each, or null. */
  readonly keyTypes = new Map<string, TypeTerm | null>();
  /** `C.x` member names TypeScript binds to a static member of the file's
   * class `C`, by span: the class. */
  staticReads = new Map<string, string>();
  /** `X.m` reads of a static member a base class of `X` declares
   * (`inheritedStatic`), by span. */
  readonly inheritedStatics = new Set<string>();
  /** `instanceof` right operands TypeScript binds to a class declared at the
   * file's top level, by span: the class. */
  readonly classTests = new Map<string, string>();
  /** `instanceof` right operands whose type TypeScript gives states
   * `[Symbol.hasInstance]`, by span. */
  readonly hookTests = new Set<string>();
  /** A `for...of` iterable's iteration intrinsic, where TypeScript's type of
   * it picks one other than `%Iterate%`, or, for a program's iterable,
   * `client`, `client-method` (its iterator's `return` a required method) or
   * `client-unclosable` (its iterator's type states no `return`), by the
   * iterable's span; likewise a spread's operand and an array pattern's
   * initializer. */
  readonly iterations = new Map<string, string>();
  /** The keys of `k in o` tests the host answers (`%HasProperty%`). */
  readonly hostIns = new Set<string>();
  /** The member names of `o.m.call(…)`, `.apply` and `.bind` TypeScript
   * resolves to a method. */
  readonly methodTargets = new Set<string>();
  /** The element reads `%ElementAt%` answers. */
  readonly hostElements = new Set<string>();
  /** The reads `for...in` bodies start with at their keys
   * (`forInEntryReads`), by span: the hidden name of the entry the loop's
   * step yields. */
  private readonly entryReads = new Map<string, string>();
  /** The well-known `Symbol.iterator`'s index among the declaration
   * document's symbols, where a program iterable is iterated. */
  wellKnownIterator: number | null = null;
  /** The standard library's well-known symbols the host reads off an
   * object a literal or a class's prototype makes (`Symbol.toStringTag`,
   * `Symbol.toPrimitive`, …), by index: keys no literal or class of the
   * fragment writes (`writtenSymbol`). */
  hostSymbols = new Set<number>();
  /** The statement being lowered, where it runs a program iterable's
   * protocol before its own code (`hoistTarget`): the spread collected, and
   * the claim sites the lowering takes from the statement. */
  private hoist: { stmt: Statement; spread: ts.SpreadElement | null;
    site: { entry(): number; span(): Span } } | null = null;
  /** The statements a lowering runs before the statement being lowered. */
  private hoisted: Stmt[] = [];
  /** The names the file assigns anywhere (`assignedNames`). */
  private assigned: Set<string> | null = null;
  /** The array pattern rest targets TypeScript types as a slice, by span. */
  readonly slices = new Set<string>();
  /** Identifiers in a class's own body TypeScript binds to that class, by
   * span: the class. */
  readonly classReads = new Map<string, string>();
  /** Identities of the declarations collected in the source type graph. */
  readonly typeIdentities = new Set<string>();
  /** Closure parameters written without a type, by the span of their name:
   * the type TypeScript gives each from its context, or why none states it. */
  readonly contextualParams = new Map<string, TypeTerm | { refused: string }>();
  /** The type TypeScript gives each static field written without an
   * annotation, by its name's span, or why none. */
  readonly staticTypes = new Map<string, TypeTerm | { refused: string }>();
  /** The callable form's annotations TypeScript infers for an
   * `Object.assign(arrow, literal)` written without type arguments, by the
   * call's span, or why none. */
  readonly assignTypes = new Map<string, { functionType: TypeTerm; bagType: TypeTerm } | { refused: string }>();
  /** Local bindings that shadow a binding of an enclosing scope, and every
   * reference TypeScript resolves to one, by the span of the identifier: the
   * name the fragment gives the binding instead (`shadowName`). */
  readonly renames = new Map<string, string>();
  /** The fragment's name of a value binding or reference spelled by `id`:
   * its own text, unless it is or names a shadowing local (`renames`). */
  local(id: Identifier): string {
    return this.renames.get(`${id.getStart(this.file)}:${id.end}`) ?? id.text;
  }
  /** The class whose instance members are being lowered: its own name reads
   * its class binding there (`selfName`). */
  private selfClass: { name: string; generic: boolean } | null = null;
  /** The classes lowered so far, by name: what a class extending one reads
   * (`classStmt`). */
  private readonly classRecords = new Map<string, ClassRecord>();
  /** The class a method being lowered inherits from: what `super.m(...)`
   * calls. */
  private superClass: ClassRecord | null = null;
  /** Calls the reviewed overlay of library globals reads as a test of the
   * calculus, `Array.isArray(e)`, and `e instanceof Array`, by span. */
  readonly globalTests = new Set<string>();
  /** Calls the reviewed overlay reads as a call of an intrinsic,
   * `Promise.resolve(v)`, by span: the intrinsic's name. */
  readonly globalIntrinsics = new Map<string, string>();
  /** The file's enums by name (PROGRAM-TYPING.md, "Enums"), each member's value as
   * TypeScript computes it, once the declaration graph has been read. */
  readonly enums = new Map<string, EnumInfo>();
  /** Reads of a `const enum` member TypeScript writes as the member's value,
   * by span: that value. */
  readonly constEnumReads = new Map<string, string | number>();
  /** Reads in an enum member's initializer of a member of the same enum,
   * bare or `E.M`, `E["M"]`, by span, with the member's span. */
  readonly enumMemberReads = new Map<string, string>();
  // Mode of the ordinary function that bound `this`, or no binding. A strict
  // arrow captures its creator's already-converted receiver; it cannot rebind it.
  private receiverMode: "strict" | "sloppy" | null = null;
  /* Whether the function whose body is being read is async: its returns
     settle the promise its call returned (`intrinsics.mts`). */
  private asyncBody = false;
  constructor(file: SourceFile) {
    this.file = file;
    this.scope = this.termScope();
  }

  /** The leading `"use strict"` directives of a directive prologue: whether
   * there is one, and how many statements the prologue's "use strict" members
   * occupy, which are dropped since they do nothing else. Another directive
   * stays an ordinary statement. */
  useStrict(statements: readonly Statement[]): {
    strict: boolean;
    skip: Set<Statement>;
  } {
    const skip = new Set<Statement>();
    for (const statement of statements) {
      if (
        !ts.isExpressionStatement(statement) ||
        !ts.isStringLiteral(statement.expression)
      )
        break;
      // The directive is the exact source text, without escapes.
      const raw = statement.expression.getText(this.file);
      if (raw === '"use strict"' || raw === "'use strict'") skip.add(statement);
    }
    return { strict: skip.size > 0, skip };
  }

  private hasTypeParam(name: string): boolean {
    return this.typeParamScopes.some((scope) => scope.has(name));
  }

  /** The name a type parameter in scope is emitted under: its spelling, or,
   * for a class's generic method, its member's binder name (`lambda`). */
  private typeParamName(name: string): string {
    for (const scope of this.typeParamScopes) {
      const emitted = scope.get(name);
      if (emitted !== undefined) return emitted;
    }
    return name;
  }

  /** The qualification a bound declares: the verifier's `Resolvable` or
   * `Awaitable`, by the declaration the file's name binds to, not shadowed by
   * a type parameter. */
  private qualificationBound(bound: TypeNode | undefined): "resolvable" | "awaitable" | null {
    if (!bound || !ts.isTypeReferenceNode(bound) || !ts.isIdentifier(bound.typeName) ||
        bound.typeArguments?.length) return null;
    const name = bound.typeName.text;
    if (this.hasTypeParam(name)) return null;
    return name === "Resolvable" && this.standardResolvable ? "resolvable"
      : name === "Awaitable" && this.standardAwaitable ? "awaitable" : null;
  }

  /** A function declaration's type parameters may be qualified
   * (`qualifiable`): `T extends Resolvable` declares it resolvable, owning
   * its observation and result, `T extends Awaitable` awaitable, owning its
   * observation; neither is a subtype bound. */
  private enterTypeParams(
    parameters: readonly TypeParameterDeclaration[] | undefined,
    rename?: (parameter: TypeParameterDeclaration, index: number) => string,
    qualifiable = false,
  ): TypeParamAst[] {
    const local = new Map<string, string>();
    const result: TypeParamAst[] = [];
    this.typeParamScopes.unshift(local);
    this.resolutionScopes.unshift(result);
    try {
      for (const [index, tp] of (parameters ?? []).entries()) {
        if (tp.defaultType)
          this.fail(tp, "type parameter defaults are outside the fragment");
        if (tp.name.kind !== ts.SyntaxKind.Identifier)
          this.fail(tp, "expected a type-parameter name");
        if (local.has(tp.name.text)) this.fail(tp, "duplicate type parameter");
        const name = rename ? rename(tp, index) : tp.name.text;
        const qualification = this.qualificationBound(tp.constraint);
        if (qualification) {
          if (!qualifiable) this.fail(tp, "Resolvable and Awaitable qualify a type parameter of a function declaration's signature");
          if (parameters?.length !== 1) this.fail(tp, "a resolution-qualified signature has exactly one source parameter");
          result.push({ name, bound: null, resolution: resolutionSlots(name, qualification) });
          local.set(tp.name.text, name);
          continue;
        }
        // A bound is any type the fragment reads; which bounds a checker can
        // use is Lean's to say.
        const bound: TypeTerm | null = tp.constraint ? this.typeOf(tp.constraint) : null;
        result.push({ name, bound, resolution: null });
        local.set(tp.name.text, name);
      }
      return result;
    } catch (error) {
      this.typeParamScopes.shift();
      this.resolutionScopes.shift();
      throw error;
    }
  }

  private leaveTypeParams(): void {
    this.resolutionScopes.shift();
    if (!this.typeParamScopes.shift())
      throw new Error("internal: no type-parameter scope to leave");
  }

  private headerTypes<T>(read: () => T): T {
    const outer = this.qualificationHeader;
    this.qualificationHeader = true;
    try { return read(); }
    finally { this.qualificationHeader = outer; }
  }

  /** A class declaration, in module initialization order: one constant per
   * method, holding a closure allocated once, whose receiver is the instance,
   * as every instance shares its prototype's method; then the class, holding
   * its constructor, which allocates an instance from the field initializers
   * and those methods. Within the fragment an instance's own fields and its
   * prototype's methods are indistinguishable. The class value is that
   * constructor as construct-only code: `new` runs it, a plain call cannot. */
  /** An enum's members, in order, with the values the declaration graph
   * reported: `null` for a member TypeScript computes no value for, whose
   * value is known only at run time (a number, as TypeScript requires). */
  enumMembers(name: string): EnumMember[] {
    const info = this.enums.get(name);
    if (!info) return this.fail(null, `enum ${name} missing`);
    return info.members.map((m) => {
      const value = m.value;
      // TypeScript's emit writes each member by assignment, which for
      // `__proto__` runs the prototype's setter and creates no property.
      if (m.name === "__proto__")
        return this.fail(m.node, "an enum member named __proto__: its assignment runs the prototype's setter, which creates no property");
      if (value === undefined) return { ...m, value: null };
      if (typeof value === "number" && !Number.isFinite(value))
        return this.fail(m.node, "an enum member that is NaN or infinite has no literal type");
      return { ...m, value };
    });
  }

  /** Whether an enum's object has keys its declaration does not name: an
   * ambient enum's, the environment's, or one with a member whose value,
   * and so whose reverse mapping's key, is known only at run time. */
  enumOpen(name: string): boolean {
    return !!this.enums.get(name)?.ambient || this.enumMembers(name).some((m) => m.value === null);
  }

  /** The type an enum's value has: its object, each member a readonly field
   * at its literal, and, for a numeric member, the reverse mapping from the
   * value's property key to the member's name, the last member with that
   * value winning (`enumEntries`). An open enum's object (`enumOpen`) states
   * its members only, one known only at run time at `number`
   * (`enumMembersTerm`). */
  enumObjectTerm(name: string, span: Span): TypeTerm {
    if (this.enumOpen(name))
      return enumMembersTerm(this.enumMembers(name).map((m) => ({ name: m.name, value: m.value ?? undefined })), span);
    return {
      k: "object",
      fields: this.enumEntries(name).map((e) => ({ name: e.key, optional: false, readonly: true,
        type: literalTerm(e.value, span), span })),
      stringIndex: null,
      calls: [],
      span,
    };
  }

  /** The type `E`: the union of its members' literal types, `number` for a
   * member whose value is known only at run time; `never` for an enum
   * without members. */
  enumTerm(name: string, span: Span): TypeTerm {
    const parts = this.enumMembers(name).map((m): TypeTerm =>
      m.value === null ? { k: "atom", name: "number", span } : literalTerm(m.value, span));
    return parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
  }

  /** The own properties of an enum's object, in JavaScript's order: array
   * index keys ascending, then the others in the order they were created.
   * TypeScript's emit creates each member's property, then, for a numeric
   * member, the property named by its value's `ToString`; a later member
   * with the same value writes that property again, which keeps its place.
   * Each entry's value has a claim site of its own: a member's at its
   * initializer, or at its name where it has none, and a reverse entry's
   * from the member to the end of the declaration. */
  enumEntries(name: string): { key: string; value: string | number; pos: Span }[] {
    const entries = new Map<string, { key: string; value: string | number; pos: Span }>();
    const members = this.enumMembers(name);
    const end = this.enums.get(name)?.end ?? 0;
    const names = new Set(members.map((m) => m.name));
    for (const m of members) {
      if (m.value === null) return this.fail(m.node, `enum ${name} has a member known only at run time`);
      entries.set(m.name, { key: m.name, value: m.value, pos: m.init ?? m.nameSpan });
      if (typeof m.value !== "number") continue;
      const key = String(m.value);
      if (names.has(key))
        this.fail(m.node, "an enum member's reverse mapping would replace a member of the same name");
      entries.set(key, { key, value: m.name, pos: [m.span[0], end] });
    }
    const index = (k: string) => /^(0|[1-9][0-9]*)$/.test(k) && Number(k) < 4294967295;
    const all = [...entries.values()];
    return [
      ...all.filter((e) => index(e.key)).sort((a, b) => Number(a.key) - Number(b.key)),
      ...all.filter((e) => !index(e.key)),
    ];
  }

  /** `enum E { … }` is the module constant `E`, bound to a fresh object whose
   * properties TypeScript's emit creates (`enumEntries`), each at a literal,
   * at the object type `enumObjectTerm`: the constant a function reading `E`
   * sees, never written, since every field is readonly.
   *
   * An enum with a member whose value is known only at run time is, first,
   * one constant `%E.M%: number` per such member, in order, bound to its
   * initializer, where a read of a member of `E` (`enumMemberReads`) is that
   * member's constant, or its value where TypeScript computes one; then `E`,
   * bound to `%Enum:E%` (`intrinsics.mts`) of the fresh object of its
   * members, which adds the reverse mapping at keys known only at run time.
   * JavaScript evaluates the initializers in the same order, writing each
   * member's property and its reverse entry between them, which only a read
   * of `E` could observe: one in an initializer is refused, and a call that
   * could read `E` before it is bound is refused by the initialization
   * order check. */
  enumStmt(node: ts.EnumDeclaration): Stmt[] {
    const name = node.name.text;
    const members = this.enumMembers(name);
    if (members.some((m) => m.value === null)) {
      // A member named by a canonical numeric string, which TypeScript
      // admits for `NaN` and `Infinity` only, may be replaced by the reverse
      // entry of a value known only at run time.
      for (const m of members)
        if (String(Number(m.name)) === m.name)
          this.fail(m.node, "an enum member named NaN or Infinity beside a member known only at run time: that member's reverse mapping may replace it");
      const stmts: Stmt[] = [];
      members.forEach((m, index) => {
        const init = m.node.initializer;
        if (m.value !== null) return;
        if (!init) return this.fail(m.node, "an enum member known only at run time needs an initializer");
        this.enumInit = { name, members, index };
        try {
          stmts.push({ k: "const", pos: m.span, bindings: [{ name: enumMemberName(name, m.name), namePos: m.nameSpan,
            annot: { k: "atom", name: "number", span: m.nameSpan }, init: this.expr(init) }] });
        } finally {
          this.enumInit = null;
        }
      });
      // The call is at the declaration from its name, the intrinsic read at
      // the name, the object at the braces, and a member's field at the
      // member, or, holding its value, at its initializer.
      const at: Span = [node.name.getStart(this.file), node.end];
      const brace: Span = [this.file.text.indexOf("{", node.name.end), node.end];
      stmts.push({ k: "const", pos: this.span(node), bindings: [{ name, namePos: this.span(node.name),
        annot: this.enumObjectTerm(name, this.span(node.name)),
        init: this.intrinsic(enumIntrinsicName(name), at, this.span(node.name), [{ k: "alloc", pos: brace,
          fields: members.map((m) => ({ name: m.name,
            e: m.value === null ? { k: "id", pos: m.span, name: enumMemberName(name, m.name) }
              : literalExpr(m.value, m.init ?? m.nameSpan) })) }]) }] });
      return stmts;
    }
    const entries = this.enumEntries(name);
    if (!entries.length)
      this.fail(node, "an enum without members allocates an object with no property, which the heap model has no record for");
    const at: Span = [node.name.getStart(this.file), node.end];
    return [{
      k: "const",
      pos: this.span(node),
      bindings: [{
        name,
        namePos: this.span(node.name),
        annot: this.enumObjectTerm(name, this.span(node.name)),
        init: {
          k: "alloc",
          pos: at,
          fields: entries.map((e) => ({ name: e.key, e: literalExpr(e.value, e.pos) })),
        },
      }],
    }];
  }

  /** The enum member initializer being lowered, of an enum with a member
   * known only at run time (`enumStmt`): its enum, members and index. */
  private enumInit: { name: string; members: EnumMember[]; index: number } | null = null;

  /** A read in `enumInit`'s initializer: of a member of its enum
   * (`enumMemberReads`), the member's constant or value, refused for a
   * member not yet initialized; any other read of the enum is of an object
   * not yet built. */
  private enumRead(node: Expression): Expr | null {
    const current = this.enumInit;
    if (!current) return null;
    const member = this.enumMemberReads.get(this.span(node).join(":"));
    if (member !== undefined) {
      const index = current.members.findIndex((m) => m.span.join(":") === member);
      const read = current.members[index];
      if (!read || index >= current.index)
        return this.fail(node, "an enum member initializer reading a member not yet initialized: JavaScript reads undefined there");
      return read.value === null ? { k: "id", pos: this.span(node), name: enumMemberName(current.name, read.name) }
        : literalExpr(read.value, this.span(node));
    }
    if (ts.isIdentifier(node) && this.local(node) === current.name)
      return this.fail(node, "an enum member initializer reading its enum: its object is not yet built");
    return null;
  }

  classStmt(node: ClassDeclaration): Stmt {
    const name = node.name;
    if (!name) return this.fail(node, "an anonymous class is outside the fragment");
    // A class extending another reads what that class's lowering recorded:
    // one declared earlier in the file. A class value from elsewhere, an
    // ambient or library class (`Array` included) and an expression are
    // outside the fragment: nothing here says what their constructors
    // allocate. Generic classes take no part in inheritance yet.
    const heritage = node.heritageClauses?.find((c) => c.token === ts.SyntaxKind.ExtendsKeyword);
    let base: ClassRecord | null = null;
    if (heritage) {
      const t = heritage.types[0];
      if (heritage.types.length !== 1 || !t || !ts.isIdentifier(t.expression))
        this.fail(heritage, "a class extends one class, by its name");
      base = this.classRecords.get(t.expression.text) ?? null;
      if (!base)
        this.fail(t, "a class extends a class declared earlier in the file; one from a library, an ambient declaration or a value is outside the fragment");
      // A generic class's binders are the declaring unit's parameter rows,
      // one per spelling: a derived class extends a generic base at the
      // base's own binders, which it declares too, so the base's
      // construction and members are at the same rows. A base at other type
      // arguments would need its construction instantiated there.
      const own = (node.typeParameters ?? []).map((tp) => tp.name.text);
      const args = t.typeArguments ?? [];
      if (base.binders.length || args.length) {
        const binders = base.binders;
        const atOwn = args.length === binders.length && args.every((a, i) =>
          ts.isTypeReferenceNode(a) && ts.isIdentifier(a.typeName) && !a.typeArguments?.length &&
          a.typeName.text === binders[i] && own.includes(a.typeName.text));
        if (!atOwn)
          this.fail(heritage, "a class extending a generic class other than at the base's own binders, which the derived class declares, is outside the fragment: the base's construction is at those binders' rows");
      }
    }
    const extended = this.file.statements.some((st) => ts.isClassDeclaration(st) &&
      !!st.heritageClauses?.some((c) => c.token === ts.SyntaxKind.ExtendsKeyword &&
        c.types.some((t) => ts.isIdentifier(t.expression) && t.expression.text === name.text)));
    if (node.modifiers?.some((m) => m.kind !== ts.SyntaxKind.ExportKeyword))
      this.fail(node, "a class modifier outside the fragment");
    const declared = this.declaredTypes.get(name.text);
    if (!declared) return this.fail(node, "a class declaration has no instance type");
    // A generic class's binders are in scope in its members; its instance
    // type is the class applied to them. Lean reads them as parameter rows of
    // the code unit that declares the class.
    const typeParams = this.enterTypeParams(node.typeParameters);
    try {
      return this.classBody(node, name, declared.declaration, typeParams, heritage, base, extended);
    } finally {
      this.leaveTypeParams();
    }
  }

  private classBody(node: ClassDeclaration, name: ts.Identifier, declaration: DeclarationIdentity,
      typeParams: TypeParamAst[], heritage: ts.HeritageClause | undefined, base: ClassRecord | null,
      extended: boolean): Stmt {
    const binders = node.typeParameters ?? [];
    const instance: TypeTerm = { k: "reference", reference: { name: name.text, span: this.span(name),
      arguments: binders.map((tp) => this.span(tp.name)), target: declaration },
      args: binders.map((tp) => ({ k: "binder", name: tp.name.text, span: this.span(tp.name) })),
      span: this.span(name) };
    const outerStrict = this.strict;
    const outerSuper = this.superClass;
    const outerSelf = this.selfClass;
    // A class body is strict code; `super.m(...)` in its methods calls its
    // base's method. Its instance members read its own name as its class
    // binding; its static members, lowered after the class value is bound,
    // read that binding directly.
    this.strict = true;
    this.superClass = base;
    const instanceMembers = { name: name.text, generic: binders.length > 0 };
    this.selfClass = instanceMembers;
    try {
      const methods: BindingAst[] = [];
      // A prototype is shared by every class instantiation. Its method
      // closures quantify the class parameters within their own contracts.
      const method = (member: MethodDeclaration, key: PropertyKey): Expr => {
        // Methods with their own binders require partial instantiation and
        // retain unit-scoped class binders.
        if (!typeParams.length || member.typeParameters?.length)
          return this.lambda(member, instance, key);
        const parameters = this.enterTypeParams(node.typeParameters,
          (_tp, index) => `${name.text}.${JSON.stringify(key)}#class${index}`);
        try {
          const receiver: TypeTerm = { ...instance,
            args: parameters.map((p, i) => ({ k: "binder", name: p.name,
              span: this.span(binders[i].name) })) };
          const closure = this.lambda(member, receiver, key);
          if (closure.k !== "lambda") throw new Error("a method lowers to a closure");
          return { ...closure, typeParams: [...parameters, ...closure.typeParams] };
        } finally {
          this.leaveTypeParams();
        }
      };
      if ((base || extended) && node.members.some((m) => {
        const memberName = nameOf(m);
        return !!memberName && ts.isPrivateIdentifier(memberName);
      }))
        this.fail(node, PRIVATE_INHERITANCE);
      // The methods its prototype holds: its base's, then its own over them.
      const methodBindings = new Map<string, string>(base?.methods ?? []);
      // The instance's own values, in the order JavaScript evaluates them:
      // field initializers and methods, parameter properties, then the
      // constructor's assignments. `bind` is where an evaluated value is
      // bound before a later constructor statement runs, at its field's type.
      type Field = { name: PropertyKey; text: string; e: Expr; bind: { pos: Span; type: TypeTerm } | null };
      const fields: Field[] = [];
      const constructors = node.members.filter(ts.isConstructorDeclaration);
      const constructor = constructors[0];
      if (constructors.length > 1) this.fail(node, "a class has one constructor");
      // Fields without an initializer hold `undefined` when the instance is
      // created (JavaScript's class fields); a constructor may assign each
      // once, as a `this.f = e` statement of its own block whose value does
      // not read `this`. Nothing else in the constructor reads `this`, so the
      // instance is complete before anything can observe it, and it is
      // allocated with its final values. Whether a field left `undefined`
      // meets its type (`x!: T` promises TypeScript it does) is Lean's check
      // of that allocation.
      const uninitialized = new Map<string, { type: TypeTerm; pos: Span; key: PropertyKey }>();
      const readsThis = (n: Node): boolean =>
        n.kind === ts.SyntaxKind.ThisKeyword ||
        (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !!n.forEachChild((c) => readsThis(c) || undefined));
      // In a static member, `super` is the base's constructor, whose statics
      // are bindings of their own, not the prototype `super.m(...)` reads.
      const readsSuper = (n: Node): boolean =>
        n.kind === ts.SyntaxKind.SuperKeyword ||
        (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !ts.isClassDeclaration(n) && !ts.isClassExpression(n) &&
          !!n.forEachChild((c) => readsSuper(c) || undefined));
      const STATIC_SUPER = "`super` in a static member is outside the fragment: it is the base's class value, which the derived class value does not hold as its prototype";
      // A derived class without a constructor has JavaScript's implicit one,
      // `constructor(...args) { super(...args); }`: it takes its base's
      // parameters, at their types, under names no source binding spells,
      // and passes them on. Actuals past them reach no parameter of the
      // base's constructor, which binds exactly its own. Each forwarded
      // read is claimed at one character of the `extends` keyword, a site
      // nothing else claims.
      type ConstructorParam = { name: string; local: string; field: string; pos: Span; property: boolean;
        at: Span; type: TypeTerm; fieldType: TypeTerm; binding: Stmt | null };
      const implicitParams = (base: ClassRecord): ConstructorParam[] => {
        const keyword = heritage ? heritage.getStart(this.file) : 0;
        if (base.params.length > "extends".length)
          this.fail(node, "an implicit derived constructor forwarding more parameters than its `extends` keyword has characters has no source site for each");
        return base.params.map((p, i) => ({ name: parameterName(i), local: parameterName(i), field: parameterName(i),
          pos: [keyword + i, keyword + i + 1], property: false, at: this.span(name), type: p.type,
          fieldType: p.type, binding: null }));
      };
      // An optional parameter, `x?: T`, binds `T | undefined`, as a closure's.
      // A parameter with a default binds a hidden name, which the caller's
      // argument initializes, and a `destructure` over it, first in the
      // constructor's body, binds the source's name, the default replacing an
      // undefined argument, as a closure's parameter with a default does.
      const params = constructor ? constructor.parameters.map((p, i, all) => {
        if (p.initializer && readsThis(p.initializer))
          this.fail(p, "a constructor parameter default that reads `this` is outside the fragment: the instance is allocated at the end of the constructor");
        if (!ts.isIdentifier(p.name) || p.dotDotDotToken)
          this.fail(p, "a constructor parameter must be plain, required or optional");
        if (!p.questionToken && !p.initializer && i > firstOptional(all))
          this.fail(p, "a required parameter cannot follow an optional one");
        if (p.name.text === "undefined") this.fail(p, "shadowing undefined is outside the fragment");
        if (p.modifiers?.length && p.name.text === "then") this.fail(p, FORGED_PROMISE);
        const local = this.local(p.name);
        const binding: Stmt | null = p.initializer ? {
          k: "destructure", pos: this.span(p), target: { k: "name", name: local, pos: this.span(p.name) },
          // The hidden name is read at the whole parameter, a site apart from
          // its name, which a parameter property's field reads again.
          default_: this.expr(p.initializer), init: { k: "id", pos: this.span(p), name: parameterName(i) },
        } : null;
        const fieldType = p.questionToken ? this.optionalTypeOf(p.type, p) : this.typeOf(p.type, p);
        return { name: p.initializer ? parameterName(i) : local, local, field: p.name.text, pos: this.span(p.name),
          property: !!p.modifiers?.length, at: this.span(p),
          // A caller may pass `undefined` where there is a default.
          type: p.initializer ? this.optionalTypeOf(p.type, p) : fieldType, fieldType, binding };
      }) : base ? implicitParams(base) : [];
      // Static methods are bindings of their own, bound first, so that
      // instance members and static initializers may call them. A static
      // field's initializer and a static block run, in member order, before
      // the class value is bound, which is allocated holding the static
      // fields: each is a binding of its own, which `C.x` in a static
      // initializer reads (`staticReads`), and the class value's own field
      // elsewhere.
      const staticMethods: BindingAst[] = [], statics: BindingAst[] = [];
      const staticFields: { name: PropertyKey; binding: string; pos: Span; type: TypeTerm }[] = [];
      // The prototype's methods, in member order: every instance holds the
      // prototype object under its prototype key, and reads a method there.
      const prototype: { name: PropertyKey; e: Expr }[] = [];
      for (const member of node.members) {
        if (ts.isSemicolonClassElement(member) || ts.isConstructorDeclaration(member)) continue;
        // A static block is code the definition runs where it stands among
        // the static fields: the closure of its statements, called at once,
        // `static { S }` as `(() => { S })()`. Its receiver is the class
        // value, whose statics are bindings of their own, so it reads no
        // `this`; its declarations are its own, as a closure body's are.
        if (ts.isClassStaticBlockDeclaration(member)) {
          if (readsThis(member.body))
            this.fail(member, "a static block that reads `this` is outside the fragment: its receiver is the class value, whose later static fields JavaScript has not defined yet and which the model allocates only after its static fields are initialized");
          if (readsSuper(member.body)) this.fail(member, STATIC_SUPER);
          this.selfClass = null;
          const start = member.getStart(this.file);
          const keyword: Span = [start, start + "static".length];
          const brace: Span = [member.body.end - 1, member.body.end];
          const stmts = this.statements(member.body.statements);
          const body: Stmt[] = completes(stmts)
            ? [...stmts, { k: "return", pos: brace, e: { k: "lit", pos: brace, lit: { a: "undefined" } } }]
            : stmts;
          const block: Expr = { k: "lambda", pos: this.span(member.body), typeParams: [], receiver: null,
            params: [], result: { k: "atom", name: "undefined", span: keyword },
            body: { k: "blockBody", pos: this.span(member.body), body } };
          statics.push({ name: staticName(name.text, `[[block@${start}]]`), namePos: keyword, annot: null,
            init: { k: "apply", pos: this.span(member), callee: block, args: [] } });
          continue;
        }
        const memberName = nameOf(member);
        if (memberName && (ts.isIdentifier(memberName) || ts.isStringLiteral(memberName)) && memberName.text === "then")
          this.fail(member, FORGED_PROMISE);
        const modifiers = childrenOf(member, "modifiers");
        if (modifiers.some((m) => m.kind !== ts.SyntaxKind.ReadonlyKeyword && m.kind !== ts.SyntaxKind.AsyncKeyword &&
            m.kind !== ts.SyntaxKind.StaticKeyword && !CLASS_ACCESS.includes(m.kind)))
          this.fail(member, "a class member modifier outside the fragment");
        this.selfClass = instanceMembers;
        if (modifiers.some((m) => m.kind === ts.SyntaxKind.StaticKeyword)) {
          // A static `[Symbol.hasInstance]` method is the binding `instanceof`
          // of the class calls (`binary`), named apart from every source name.
          // A static private member `#x` is a binding as any static is,
          // which `C.#x` in the class reads (`staticPrivate`).
          const hasInstance = ts.isMethodDeclaration(member) && this.staticHasInstance(member.name);
          if (!(ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) ||
              (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name) && !hasInstance))
            return this.fail(member, unnamedMember(member, true));
          const binding = staticName(name.text,
            ts.isIdentifier(member.name) || ts.isPrivateIdentifier(member.name) ? member.name.text : HAS_INSTANCE);
          if (ts.isMethodDeclaration(member)) {
            // `C.m()` passes `C` as the receiver, a detached call `undefined`:
            // a body that reads none is the same function either way, called
            // plainly. Its signature is its annotation: functions read it there.
            // It is bound first, before the class value, which it reads, as
            // an instance member does, as the class's own binding.
            if (member.body && readsThis(member.body))
              this.fail(member, "a static method that reads `this` is outside the fragment");
            if (member.body && readsSuper(member.body)) this.fail(member, STATIC_SUPER);
            const annot = member.type && !member.typeParameters?.length
              ? signature(this.scope, member.parameters, member.type, member, this.span(member), true) : null;
            staticMethods.push({ name: binding, namePos: this.span(member.name), annot, init: this.lambda(member) });
            // A static method keyed by a symbol is also an own property of
            // the class value, at its signature, which no copy takes, as no
            // copy takes a symbol key (or, in JavaScript, a method).
            if (hasInstance && ts.isComputedPropertyName(member.name)) {
              const symbol = this.symbolKeys.get(this.span(member.name.expression).join(":"));
              if (symbol === undefined || !annot)
                this.fail(member, "a static method keyed by a symbol is an own property of the class value, at its annotated signature");
              staticFields.push({ name: { symbol }, binding, pos: this.span(member.name), type: annot });
            }
            continue;
          }
          this.selfClass = null;
          // A static field's writes would be mutable module state.
          if (!modifiers.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword) || member.postfixToken)
            this.fail(member, "a static field must be readonly and required");
          if (member.initializer && readsThis(member.initializer))
            this.fail(member, "a static initializer that reads `this` is outside the fragment");
          if (member.initializer && readsSuper(member.initializer)) this.fail(member, STATIC_SUPER);
          const annot = member.type ? this.typeOf(member.type, member) : null;
          statics.push({ name: binding, namePos: this.span(member.name), annot,
            init: member.initializer ? this.expr(member.initializer)
              : { k: "lit", pos: this.span(member.name), lit: { a: "undefined" } } });
          // A static field named by a property name is an own enumerable
          // data property of the class value, which the class value is
          // allocated holding, at the type its annotation states, or, without
          // one, the literal type TypeScript gives a readonly field's literal
          // initializer.
          if (ts.isIdentifier(member.name)) {
            const inferred = annot ? null : this.staticTypes.get(this.span(member.name).join(":"));
            if (!annot && (!inferred || "refused" in inferred))
              this.fail(member, `a static field without an annotation, whose type TypeScript gives no term of the fragment states: ${inferred && "refused" in inferred ? inferred.refused : "no type"}`);
            const type = annot ?? (inferred && !("refused" in inferred) ? inferred : this.fail(member, "a static field's type"));
            staticFields.push({ name: member.name.text, binding, pos: this.span(member.name), type });
          }
          continue;
        }
        if (ts.isPropertyDeclaration(member)) {
          // A private field `#x` is an own key of each instance, its private
          // name's symbol (`memberKey`).
          if (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name))
            this.fail(member, unnamedMember(member, false));
          const key = this.memberKey(member.name);
          const type = this.typeOf(member.type, member);
          if (member.initializer) {
            if (readsThis(member.initializer)) this.fail(member, "a field initializer that reads `this` is outside the fragment");
            fields.push({ name: key, text: member.name.text, e: this.expr(member.initializer),
              bind: { pos: this.span(member), type } });
          } else uninitialized.set(member.name.text, { type, pos: this.span(member.name), key });
        } else if (ts.isMethodDeclaration(member)) {
          // A method named by a `unique symbol` constant, `[Symbol.iterator]()`,
          // is the prototype's property under that symbol's key, bound under
          // a name no source spells.
          const symbol = ts.isComputedPropertyName(member.name) ? this.writtenSymbol(member.name, member) : null;
          if (symbol !== null) {
            if (member.asteriskToken)
              this.fail(member, GENERATOR);
            const binding = `${name.text}.[symbol ${symbol}]`;
            methods.push({ name: binding, namePos: this.span(member.name), annot: null,
              init: method(member, { symbol }) });
            prototype.push({ name: { symbol }, e: { k: "id", pos: this.span(member.name), name: binding } });
            continue;
          }
          // A private method `#m` is held by the prototype under its private
          // name's symbol, as a method under its name; a derived class
          // reaches none, so it is no base method.
          if (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name))
            this.fail(member, unnamedMember(member, false));
          methods.push({ name: `${name.text}.${member.name.text}`, namePos: this.span(member.name),
            annot: null, init: method(member, this.memberKey(member.name)) });
          if (ts.isIdentifier(member.name))
            methodBindings.set(member.name.text, `${name.text}.${member.name.text}`);
          prototype.push({ name: this.memberKey(member.name),
            e: { k: "id", pos: this.span(member.name), name: `${name.text}.${member.name.text}` } });
        } else this.fail(member, classMemberRefusal(member));
      }
      this.selfClass = instanceMembers;
      for (const p of params)
        if (p.property) fields.push({ name: p.field, text: p.field, e: { k: "id", pos: p.pos, name: p.local }, bind: { pos: p.at, type: p.fieldType } });
      // A class allocates its prototype object once, holding its methods, and
      // each instance holds it under the prototype key, first: the key's
      // value is a read of a constant, so its place changes nothing. A
      // derived class's prototype holds its own methods and links to its
      // base's under the prototype key, as JavaScript's does. A class that
      // `instanceof` tests owns its key there. A prototype holding nothing
      // of its own, which nothing tests, is not allocated: its instances
      // hold its base's, or none, and every read and test answers alike.
      const prototypeBinding: BindingAst[] = [];
      let proto: Expr | null = null;
      let protoBinding: string | null = null;
      const baseType = heritage?.types[0];
      const baseProto: Expr | null = base?.proto && baseType
        ? { k: "id", pos: this.span(baseType.expression), name: base.proto } : null;
      const tested = [...this.classTests.values()].includes(name.text);
      if (!prototype.length && !tested && base?.proto) protoBinding = base.proto;
      if (prototype.length || tested) {
        const at: Span = [name.getStart(this.file), node.end];
        protoBinding = prototypeName(name.text);
        prototypeBinding.push({ name: prototypeName(name.text), namePos: at, annot: null,
          init: { k: "alloc", pos: at, fields: prototype, ...(baseProto ? { proto: baseProto } : {}),
            ...(tested ? { brand: { key: classKey(name.text), pos: [name.end, node.end] } } : {}) } });
      }
      if (protoBinding) {
        // Read at the `class` keyword, a site no other claim has; the
        // allocation states it apart from the fields, as no source key.
        const keyword = this.file.text.indexOf("class", node.getStart(this.file));
        if (keyword < 0 || keyword > name.getStart(this.file)) this.fail(node, "a class declaration without its keyword");
        proto = { k: "id", pos: [keyword, keyword + "class".length], name: protoBinding };
      }
      // A `return` in a constructor's own code, outside any function nested
      // in it: `new` would evaluate to the instance, not to what it returns.
      const nested = (n: Node): boolean => ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) ||
        ts.isArrowFunction(n) || ts.isMethodDeclaration(n) || ts.isClassDeclaration(n) || ts.isClassExpression(n);
      const returns = (n: Node): boolean => ts.isReturnStatement(n) ||
        (!nested(n) && !!n.forEachChild((c) => returns(c) || undefined));
      const assignment = (statement: Statement) => {
        const e = ts.isExpressionStatement(statement) ? statement.expression : undefined;
        return e && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
          ts.isPropertyAccessExpression(e.left) && e.left.expression.kind === ts.SyntaxKind.ThisKeyword &&
          (ts.isIdentifier(e.left.name) || ts.isPrivateIdentifier(e.left.name))
          ? { field: e.left.name.text, value: e.right } : undefined;
      };
      const assigns = (statement: Statement): boolean => !!assignment(statement) ||
        (ts.isBlock(statement) && statement.statements.some(assigns)) ||
        (ts.isIfStatement(statement) && (assigns(statement.thenStatement) ||
          (!!statement.elseStatement && assigns(statement.elseStatement))));
      // The constructor's statements from `body` on, then its allocation.
      // Statements other than field assignments run before the allocation:
      // the values evaluated before one are bound first, in order, to names
      // no source binding can spell, so evaluation order is the source's. A
      // last `if` that assigns fields ends each arm with its own allocation.
      const construct = (body: readonly Statement[], before: Field[], done: Set<string>,
          prelude: Stmt[] = [], end: Span | null = null): Stmt[] => {
        const fields = before.map((f) => ({ ...f }));
        const assigned = new Set(done);
        const statements: Stmt[] = [...prelude];
        let branched = false;
        const flush = () => {
          for (const f of fields) {
            if (!f.bind || f.e.k === "lit") continue;
            const hidden = `this.${f.text}`;
            statements.push({ k: "const", pos: f.bind.pos,
              bindings: [{ name: hidden, namePos: f.bind.pos, annot: f.bind.type, init: f.e }] });
            f.e = { k: "id", pos: f.bind.pos, name: hidden };
            f.bind = null;
          }
        };
        for (const [i, statement] of body.entries()) {
          const assigning = assignment(statement);
          if (assigning) {
            const field = uninitialized.get(assigning.field);
            if (!field || assigned.has(assigning.field))
              this.fail(statement, "a constructor assigns each uninitialized field once");
            if (readsThis(assigning.value))
              this.fail(statement, "a constructor assignment that reads `this` is outside the fragment");
            assigned.add(assigning.field);
            fields.push({ name: field.key, text: assigning.field, e: this.expr(assigning.value),
              bind: { pos: this.span(statement), type: field.type } });
            continue;
          }
          if (ts.isIfStatement(statement) && assigns(statement) && i === body.length - 1) {
            if (readsThis(statement.expression))
              this.fail(statement, "a constructor statement that reads `this` is outside the fragment");
            // An unbraced arm, `else if` included, is the one statement a
            // block around it would hold.
            // Each arm's allocation is its own statement, entered at the
            // arm's last character, or, with no `else`, at the condition's
            // closing parenthesis.
            const arm = (s: Statement | undefined): Stmt[] =>
              construct(!s ? [] : ts.isBlock(s) ? s.statements : [s], fields, assigned, [],
                s ? [s.end - 1, s.end] : conditionParen(statement, this.file));
            flush();
            statements.push({ k: "if", pos: this.span(statement), cond: this.expr(statement.expression),
              then: arm(statement.thenStatement), else_: arm(statement.elseStatement) });
            branched = true;
            break;
          }
          if (returns(statement))
            this.fail(statement, "a constructor does not return");
          if (readsThis(statement))
            this.fail(statement, assigns(statement)
              ? "a constructor assigns fields in its own block, or in the arms of its last `if`"
              : "a constructor statement that reads `this` is outside the fragment");
          flush();
          statements.push(this.stmt(statement));
        }
        if (!branched) {
          for (const [f, { pos, key }] of uninitialized)
            if (!assigned.has(f)) fields.push({ name: key, text: f, e: { k: "lit", pos, lit: { a: "undefined" } }, bind: null });
          // The allocation ends the constructor's block: the instance is what
          // `new` evaluates to. A derived instance is its base's part, copied,
          // then its own fields over it: the allocation from parts an object
          // literal with a spread is.
          const at = this.span(name);
          const instanceValue: Expr = derivedBase
            ? { k: "build", pos: at, parts: [{ spread: derivedBase },
                ...fields.map(({ name, e }) => ({ name: typeof name === "string" ? name : this.fail(node, PRIVATE_INHERITANCE), e }))],
                ...(proto ? { proto } : {}) }
            : { k: "alloc", pos: at, fields: fields.map(({ name, e }) => ({ name, e })),
              ...(proto ? { proto } : {}) };
          statements.push({ k: "return", pos: end ?? at, e: instanceValue });
        }
        return statements;
      };
      // A derived constructor: its statements before `super(...)`, which may
      // not touch `this`, then the base's constructor at the actuals, bound
      // to a name no source binding spells, then its own fields and
      // statements, as JavaScript runs them.
      let body: readonly Statement[] = constructor?.body?.statements ?? [];
      let prelude: Stmt[] = [];
      let derivedBase: Expr | null = null;
      if (base && heritage) {
        const isSuperCall = (st: Statement): st is ts.ExpressionStatement =>
          ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) &&
          st.expression.expression.kind === ts.SyntaxKind.SuperKeyword;
        const callsSuper = (n: Node): boolean => n.kind === ts.SyntaxKind.SuperKeyword ||
          (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !!n.forEachChild((c) => callsSuper(c) || undefined));
        let at: Span = this.span(heritage);
        let calleeAt: Span = [node.end - 1, node.end];
        let actuals: Expr[] = params.map((p) => ({ k: "id", pos: p.pos, name: p.name }));
        if (constructor) {
          const index = body.findIndex(isSuperCall);
          if (index < 0 || body.some((st, i) => i !== index && callsSuper(st)))
            this.fail(constructor, "a derived constructor calls `super(...)` once, as a statement of its own body");
          for (const st of body.slice(0, index))
            if (readsThis(st))
              this.fail(st, "`this` before `super(...)` throws in JavaScript; the instance is allocated at the end of the constructor, so a read or write of it there is refused");
          prelude = body.slice(0, index).map((st) => this.stmt(st));
          const superCall = body[index];
          const call = superCall && ts.isExpressionStatement(superCall) && ts.isCallExpression(superCall.expression)
            ? superCall.expression
            : this.fail(constructor, "a derived constructor calls `super(...)` once, as a statement of its own body");
          for (const a of call.arguments)
            if (ts.isSpreadElement(a) || readsThis(a)) this.fail(a, "a `super(...)` argument is an ordinary expression not reading `this`");
          actuals = call.arguments.map((a) => this.expr(a));
          at = this.span(call);
          calleeAt = this.span(call.expression);
          body = body.slice(index + 1);
        }
        const slot = baseName(name.text);
        prelude.push({ k: "const", pos: at, bindings: [{ name: slot, namePos: at, annot: null,
          init: { k: "new", pos: at, callee: { k: "id", pos: calleeAt, name: base.fresh }, args: actuals } }] });
        derivedBase = { k: "id", pos: [heritage.getStart(this.file), heritage.getStart(this.file) + "extends".length], name: slot };
      }
      // The class value is its constructor as construct-only code, which only
      // `new` runs, holding its static fields.
      // A static field names none of the class's binders (TypeScript refuses
      // one that does), so a generic class value's bag is the same at each
      // of its instances.
      // A static initializer constructing the class constructs it through
      // its construct-only code, bound before them (`selfConstruction`).
      const constructs = node.members.some((m) => {
        let found = false;
        const visit = (n: Node): void => {
          if (ts.isNewExpression(n) && ts.isIdentifier(n.expression) &&
              this.classReads.get(this.span(n.expression).join(":")) === name.text) found = true;
          n.forEachChild(visit);
        };
        if ((ts.isPropertyDeclaration(m) && m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword)) ||
            ts.isClassStaticBlockDeclaration(m)) visit(m);
        return found;
      });
      const constructorLambda: Expr = { k: "lambda", pos: this.span(node),
        typeParams: [], receiver: null, params: params.map((p) => ({ name: p.name, type: p.type })),
        result: instance, body: { k: "blockBody", pos: this.span(constructor?.body ?? node),
          body: [...params.flatMap((p) => p.binding ? [p.binding] : []),
            ...construct(body, fields, new Set(), prelude)] } };
      const lambda: Expr = { k: "ctor", pos: this.span(node), ...(typeParams.length ? { typeParams } : {}),
        // Its code is the construct-only code bound before the static
        // initializers, where they construct the class (`decodeBindings`).
        lambda: constructs || extended ? { k: "id", pos: this.span(name), name: freshName(name.text) } : constructorLambda,
        ...(staticFields.length ? { statics: staticFields.map((f) =>
          ({ name: f.name, e: { k: "id", pos: f.pos, name: f.binding } satisfies Expr })) } : {}) };
      const type: TypeTerm = { k: "constructor", params: params.map((p) => p.type), rest: null, result: instance,
        ...(staticFields.length ? { statics: staticFields.map((f) => ({ name: f.name, type: f.type })) } : {}),
        span: this.span(name) };
      // A class another extends is also bound, first, as its fresh
      // constructor, claimed at the instance it allocates besides its own
      // construct signature; the class value is that binding.
      // A class another extends, or whose static initializers construct it,
      // is also bound, first, as its fresh constructor, before its static
      // initializers, claimed at the instance it allocates besides its own
      // construct signature: a derived class's construction, and a static
      // initializer's (`selfConstruction`), construct through it. The class
      // value is that binding, or, holding static fields, its constructor
      // allocated again with them (`decodeBindings`).
      let freshBinding: BindingAst[] = [];
      let classBindings: BindingAst[] = [{ name: name.text, namePos: this.span(name), annot: type, init: lambda }];
      if (extended || constructs) {
        const brace = this.file.text.indexOf("{", heritage ? heritage.end : name.end);
        freshBinding = [{ name: freshName(name.text), namePos: [node.getStart(this.file), name.end], annot: null,
          init: { k: "ctor", pos: [node.getStart(this.file), name.end], ...(typeParams.length ? { typeParams } : {}),
            lambda: constructorLambda } }];
        classBindings = [{ name: name.text, namePos: this.span(name), annot: type,
          init: staticFields.length ? lambda : { k: "id", pos: [brace, brace + 1], name: freshName(name.text) } }];
      }
      this.classRecords.set(name.text, { params: params.map((p) => ({ name: p.name, type: p.type })),
        methods: methodBindings, fresh: freshName(name.text), proto: protoBinding,
        binders: binders.map((tp) => tp.name.text) });
      return { k: "const", pos: this.span(node),
        bindings: [...staticMethods, ...methods, ...prototypeBinding, ...freshBinding, ...statics, ...classBindings] };
    } finally {
      this.strict = outerStrict;
      this.superClass = outerSuper;
      this.selfClass = outerSelf;
    }
  }

  registerDeclaredType(name: string, required: number, total: number,
      declaration: DeclarationIdentity, node: Node, expression: TypeTerm): void {
    if (this.declaredTypes.has(name))
      this.fail(node, "duplicate type name");
    this.declaredTypes.set(name, { required, total, declaration });
    if (expression.k === "array" || expression.k === "tuple" || expression.k === "reference")
      this.aliasEquations.set(name, { total, declaration, expression });
  }

  fail(node: Node | null, message: string): never {
    const start = node ? node.getStart(this.file) : 0;
    const at = this.file.getLineAndCharacterOfPosition(start);
    throw new Error(
      `gate: ${message} (line ${at.line + 1}, col ${at.character + 1})`,
    );
  }

  span(node: Node): Span {
    return [node.getStart(this.file), node.end];
  }

  /** The key a member name spells: its text, or a private name's symbol,
   * the key of the member TypeScript binds it to, which no code outside
   * the class spells. */
  private memberKey(name: ts.MemberName): PropertyKey {
    if (ts.isIdentifier(name)) return name.text;
    const symbol = this.privateKeys.get(this.span(name).join(":"));
    if (symbol === undefined) return this.fail(name, "a private name TypeScript binds to no member");
    return { symbol };
  }

  /** `C.#x` of a static private member of the file's class `C`, with `C`
   * the class TypeScript binds it to: the binding the class statement gives
   * the member. Null for a private name no static member declares. */
  private staticPrivate(node: ts.PropertyAccessExpression): { binding: string; cls: string } | null {
    const name = node.name;
    if (!ts.isPrivateIdentifier(name)) return null;
    const symbol = this.privateKeys.get(this.span(name).join(":"));
    const cls = symbol === undefined ? undefined : this.symbolIdentities[symbol]?.name.split(".")[0];
    const declaration = cls === undefined ? undefined : this.file.statements.find((st): st is ClassDeclaration =>
      ts.isClassDeclaration(st) && st.name?.text === cls);
    const member = declaration?.members.find((m) => {
      const memberName = nameOf(m);
      return !!memberName && ts.isPrivateIdentifier(memberName) && memberName.text === name.text;
    });
    if (!cls || !member || !isStatic(member))
      return null;
    if (!ts.isIdentifier(node.expression) || this.classReads.get(this.span(node.expression).join(":")) !== cls)
      this.fail(node, "a static private member read other than through its class's name: private statics are bindings of their own");
    return { binding: staticName(cls, name.text), cls };
  }

  /** `new C(…)` in a static initializer of `C`, which runs before the class
   * value exists: the class's construct-only code, bound before the static
   * initializers (`freshName`), where constructing runs no code that
   * could read the class value (`selfConstructs`). Null for any other `new`. */
  private selfConstruction(node: ts.NewExpression): Expr | null {
    const callee = node.expression;
    if (!ts.isIdentifier(callee)) return null;
    const cls = this.classReads.get(this.span(callee).join(":"));
    const init = this.staticInitOf(node);
    if (cls === undefined || init?.cls !== cls || init.closure) return null;
    const declaration = this.file.statements.find((st): st is ClassDeclaration =>
      ts.isClassDeclaration(st) && st.name?.text === cls);
    if (!declaration || !selfConstructs(declaration))
      this.fail(node, "a static initializer constructing its class where constructing it reads the class or runs code, or another static initializer runs code: it could read a static field not yet defined, `undefined` in JavaScript, or the class value, which the model allocates only after its static fields are initialized");
    return { k: "id", pos: this.span(callee), name: freshName(cls) };
  }

  /** Whether `body` reads class `cls`: an identifier TypeScript binds to it. */
  private readsClass(body: Node, cls: string): boolean {
    const visit = (n: Node): boolean =>
      (ts.isIdentifier(n) && this.classReads.get(this.span(n).join(":")) === cls) ||
      !!n.forEachChild((c) => visit(c) || undefined);
    return visit(body);
  }

  /** The class whose static field initializer or static block `node` is in,
   * and whether a closure created there holds it. */
  private staticInitOf(node: Node): { cls: string; closure: boolean } | null {
    let closure = false;
    for (let at: Node = node; at.parent; at = at.parent) {
      const parent = at.parent;
      if (ts.isClassDeclaration(parent)) {
        const isStaticInit = ts.isClassStaticBlockDeclaration(at) ||
          (ts.isPropertyDeclaration(at) && at.initializer !== undefined &&
            !!at.modifiers?.some((m) => m.kind === ts.SyntaxKind.StaticKeyword));
        return isStaticInit && parent.name ? { cls: parent.name.text, closure } : null;
      }
      if (ts.isFunctionLikeDeclaration(at)) closure = true;
    }
    return null;
  }

  /** The class binding an identifier of an instance member reads, where
   * TypeScript binds it to the class being lowered. */
  private ownClass(node: Node): string | null {
    const cls = this.classReads.get(this.span(node).join(":"));
    if (!cls || cls !== this.selfClass?.name) return null;
    if (this.selfClass.generic)
      this.fail(node, "a generic class's instance member or static method reading its own class: the class value is quantified over the binders its declaring unit reads as parameter rows, and a module value is read only at ground instances");
    return selfName(cls);
  }

  /* ------------------------------------------------------ async, await -- */
  // `async` and `await` are trusted steps, written as calls of intrinsics
  // (`intrinsics.mts`): the call is at `pos`, the intrinsic read at `at`.

  private intrinsic(name: string, pos: Span, at: Span, args: Expr[]): Expr {
    return { k: "apply", pos, callee: { k: "id", pos: at, name }, args };
  }

  /** A spread argument's operand. Over a string, a `Set`, a `Map` or a host
   * collection iterator, which TypeScript's type of it decides, `...x` is
   * `...%Spread:K%(x)`: the fresh array of the elements its iterator yields
   * (`intrinsics.mts`), the call at the spread, the intrinsic read at `...`.
   * An array is spread as it is. A program's iterable is collected into a
   * fresh array before the statement (`collect`), where that runs its code in
   * its place (`hoistTarget`). */
  private spreadOperand(arg: ts.SpreadElement): Expr {
    const intrinsic = this.iterations.get(this.span(arg.expression).join(":"));
    if (intrinsic?.startsWith("client")) {
      if (this.hoist?.spread !== arg) this.fail(arg, SPREAD_POSITION);
      return this.collect(arg.expression);
    }
    const operand = this.expr(arg.expression);
    if (!intrinsic) return operand;
    const start = arg.getStart(this.file);
    return this.intrinsic(intrinsic, this.span(arg), [start, start + "...".length], [operand]);
  }

  /** The symbol a computed key names where it is a `unique symbol` constant
   * a literal or a class may write: `Symbol.iterator`, `Symbol.hasInstance`
   * (an ordinary key of these objects: `instanceof` alone reads it, off its
   * right operand), or one of the program's own. Another of
   * the standard library's well-known symbols is refused: each changes how
   * the host treats the object (`Object.prototype.toString`, conversions,
   * `for await`), which the model does not state, and `Symbol.toStringTag`
   * would let the object pass for a host `Set` or `Map`, whose iteration is
   * trusted to be the host's. */
  private writtenSymbol(name: ts.ComputedPropertyName, at: Node): number | null {
    const symbol = this.symbolNames.get(this.span(name.expression).join(":"));
    if (typeof symbol !== "number") return null;
    if (this.hostSymbols.has(symbol))
      this.fail(at, "a well-known symbol key other than `Symbol.iterator` and `Symbol.hasInstance` is outside the fragment: it changes how the host treats the object, which the model does not state, and `Symbol.toStringTag` would let it pass for a host collection whose iteration is trusted");
    return symbol;
  }

  /** `await e`: `%Await%(e)`, the intrinsic read at the keyword. Every span
   * an intrinsic call or read is given is a node or a token of the source. */
  private awaitExpr(node: ts.AwaitExpression): Expr {
    const start = node.getStart(this.file);
    return this.intrinsic(awaitName, this.span(node), [start, start + "await".length],
      [this.expr(node.expression)]);
  }

  /** An async body completes with `return %AsyncComplete%()`: the call spans
   * the block, the intrinsic and the statement its closing brace. Nothing is
   * added to a body that returns on every path. */
  private asyncCompletion(block: ts.Block, statements: Stmt[]): Stmt[] {
    const returns = (xs: Stmt[]): boolean => {
      const last = xs.at(-1);
      return last?.k === "return" || last?.k === "throw" ||
        (last?.k === "if" && last.else_ !== null && returns(last.then) && returns(last.else_)) ||
        (last?.k === "try" && ((last.finalizer !== null && returns(last.finalizer)) ||
          (returns(last.body) && (last.handler === null || returns(last.handler.body)))));
    };
    if (returns(statements)) return statements;
    const brace: Span = [block.end - 1, block.end];
    return [...statements, { k: "return", pos: brace,
      e: this.intrinsic(asyncCompleteName, this.span(block), brace, []) }];
  }

  text(node: Node): string {
    return this.file.text.slice(node.getStart(this.file), node.end);
  }

  /* ------------------------------------------------------------- types -- */

  /** Type syntax reads through the one source-term reader. A name is a
   * binder of an enclosing function or a declaration root; every declaration
   * root was resolved by TypeScript's checker. */
  private readonly scope: TermScope;
  private termScope(): TermScope {
    return {
      source: this.file,
      annotation: true,
      awaited: node => this.standardAwaited && ts.isIdentifier(node.typeName) &&
        node.typeName.text === "Awaited" && !this.hasTypeParam("Awaited"),
      associatedAlias: node => ts.isIdentifier(node.typeName) && !this.hasTypeParam(node.typeName.text)
        ? this.resolutionAliases.get(node.typeName.text) ?? null : null,
      associated: (input, span, node) => {
        const owner = input.k === "binder" ? this.resolutionScopes.flat()
          .find(p => p.name === input.name) : undefined;
        if (!owner) return this.fail(node, "Awaited requires the input of a resolution-qualified parameter");
        if (!owner.resolution) {
          if (!this.qualificationHeader) return this.fail(node,
            "Awaited cannot add a qualification to an ordinary function body");
          const parameters = this.resolutionScopes.find(ps => ps.includes(owner));
          if (parameters?.length !== 1) return this.fail(node,
            "a resolution-qualified signature has exactly one source parameter");
          owner.resolution = resolutionSlots(owner.name, "resolvable");
        }
        if (owner.resolution.result === null)
          return this.fail(node, "Awaited requires a resolvable parameter: an awaitable one owns no result");
        return { k: "binder", name: owner.resolution.result, span };
      },
      fail: (node, message) => this.fail(node, message),
      enumerated: (node, span) => {
        // `E.A`, a member's literal type, and `typeof E`, the enum's object.
        if (ts.isTypeQueryNode(node) && ts.isIdentifier(node.exprName) && this.enums.has(node.exprName.text) &&
            !node.typeArguments?.length)
          return this.enumObjectTerm(node.exprName.text, span);
        if (ts.isTypeReferenceNode(node) && ts.isQualifiedName(node.typeName) &&
            ts.isIdentifier(node.typeName.left) && this.enums.has(node.typeName.left.text)) {
          const member = node.typeName.right.text;
          const found = this.enumMembers(node.typeName.left.text).find((m) => m.name === member);
          if (found) return found.value === null ? { k: "atom", name: "number", span } : literalTerm(found.value, span);
        }
        return null;
      },
      symbol: (name) => {
        const [start, end] = this.span(name);
        const result = this.symbolNames.get(`${start}:${end}`);
        if (result === undefined) return this.fail(name, "a computed key names a symbol constant");
        if (typeof result !== "number") return this.fail(name, result.refused);
        return result;
      },
      keys: (node) => this.keyTypes.get(this.span(node).join(":")) ?? null,
      // The alias the reference names, as TypeScript resolved it, at every
      // one of its parameters.
      equation: (reference) => {
        const alias = this.aliasEquations.get(reference.reference.name);
        const target = reference.reference.target;
        if (!alias || reference.args.length !== alias.total || !target ||
            target.module !== alias.declaration.module || target.name !== alias.declaration.name ||
            target.span[0] !== alias.declaration.span[0] || target.span[1] !== alias.declaration.span[1])
          return null;
        return substitute(alias.expression, reference.args);
      },
      computed: (node, span) => {
        const result = this.computedTypes.get(`${span[0]}:${span[1]}`);
        if (!result) return this.fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
        if ("refused" in result) return this.fail(node, result.refused);
        return result;
      },
      named: (node, span, read) => {
        const name = ts.isIdentifier(node.typeName) ? node.typeName.text
          : this.fail(node, "type reference outside the fragment");
        // An application of an alias TypeScript computes from its parameters
        // is a computed type, evaluated where it is written.
        const computed = this.hasTypeParam(name) ? undefined : this.computedTypes.get(`${span[0]}:${span[1]}`);
        if (computed) {
          if ("refused" in computed) return this.fail(node, computed.refused);
          return computed;
        }
        if (this.enums.has(name) && !this.hasTypeParam(name)) {
          if (node.typeArguments?.length) this.fail(node, "an enum type takes no type arguments");
          return this.enumTerm(name, span);
        }
        const library = this.libraryTypes.get(name);
        if (library !== undefined && !this.hasTypeParam(name))
          return libraryTerm(library, libraryArguments(library, node.typeArguments ?? [], read,
            part => this.keyTypes.get(this.span(part).join(":")) ?? null), span,
            message => this.fail(node, message));
        const declared = this.declaredTypes.get(name);
        if (declared !== undefined && !this.hasTypeParam(name)) {
          const args = node.typeArguments ?? [];
          if (args.length < declared.required || args.length > declared.total) {
            const count = declared.required === declared.total
              ? `${declared.total}`
              : `${declared.required} to ${declared.total}`;
            this.fail(node, `type '${name}' needs ${count} type argument(s)`);
          }
          return { k: "reference", reference: { name, span,
            arguments: args.map(arg => this.span(arg)), target: declared.declaration },
            args: args.map(read), span };
        }
        if (node.typeArguments?.length) this.fail(node, "unknown type alias");
        if (!this.hasTypeParam(name)) this.fail(node, "unknown type parameter");
        return { k: "binder", name: this.typeParamName(name), span };
      },
    };
  }

  typeOf(node: TypeNode | undefined, at: Node | null = null): TypeTerm {
    return typeTerm(this.scope, node, at);
  }

  /** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
   * value bound when a call omits that position. The fragment carries the
   * union, so nothing downstream needs a second representation of optionality.
   * A call may omit a trailing position exactly when its contract admits
   * `undefined`; declared arity is not observable in this fragment. */
  optionalTypeOf(node: TypeNode | undefined, at: Node): TypeTerm {
    return optionalTerm(this.typeOf(node, at), this.span(at));
  }

  /** A closure parameter's contract: its annotation, or, without one, the
   * type TypeScript gives it from its context (an optional one's includes
   * `undefined` already). That type is a proposal like any claim: the body
   * is checked at it, and the closure's signature wherever the closure
   * goes, the call offering it included. Its declarations belong to the shared
   * declaration graph, and its type parameters are in scope. */
  private closureParamType(p: ts.ParameterDeclaration): TypeTerm {
    if (p.type || p.dotDotDotToken) return p.questionToken ? this.optionalTypeOf(p.type, p) : this.typeOf(p.type, p);
    const found = this.contextualParams.get(this.span(p.name).join(":"));
    if (!found) return this.typeOf(undefined, p);
    if ("refused" in found) return this.fail(p, found.refused);
    visitType(found, (t, bound) => {
      if (t.k === "reference") {
        const target = t.reference.target;
        if (!this.typeIdentities.has(JSON.stringify([target.module, target.span, target.name])))
          this.fail(p, `contextual type declaration missing: ${t.reference.name}`);
      }
      if (t.k === "binder" && !bound.has(t.name) && !this.hasTypeParam(t.name))
        this.fail(p, `TypeScript types this unannotated closure parameter from its context at the type parameter ${t.name}, not one in scope here`);
    });
    return found;
  }

  /** A rest parameter's contract: its tuple of required positions or its
   * array, the collected array viewed at it. A declared alias is read
   * through its equation, as TypeScript reads one: the parameter's type is
   * that equation. */
  restType(p: ParameterDeclaration): TypeTerm {
    const type = restTerm(this.scope, this.typeOf(p.type, p));
    if (!restPositions(type)) this.fail(p, restRefusal(type));
    return type;
  }

  /** A module function's rest parameter: as any rest's (`restType`), or
   * typed by one of the function's own type parameters, `...args: T`. That
   * parameter is then an argument pack: each call instantiates it at the
   * list of actuals it collects, within its bound, an array or a tuple of
   * required positions written as one. The body sees the fresh array at
   * that bound, the elements every instance's list has; the parameter types
   * nothing else, since the collected array is no value of it. */
  private moduleRestType(p: ParameterDeclaration, node: FunctionDeclaration): TypeTerm {
    const name = p.type && ts.isTypeReferenceNode(p.type) && ts.isIdentifier(p.type.typeName) &&
      !p.type.typeArguments ? p.type.typeName.text : null;
    const own = node.typeParameters?.find(tp => tp.name.text === name);
    if (!p.type || !own) return this.restType(p);
    const written = this.typeOf(p.type, p);
    if (written.k !== "binder") return this.restType(p);
    if (typeParameterMentioned(node, own, p.type)) this.fail(p, REST_PACK_VALUE);
    const bound = own.constraint ? this.typeOf(own.constraint) : null;
    if (!bound || !restPositions(bound)) this.fail(p, REST_PACK_BOUND);
    return { k: "pack", of: written, span: this.span(p) };
  }

  /* ------------------------------------------------------- expressions -- */

  expr(node: Expression): Expr {
    // As in `atomsOf`: Expression is one base interface, so each form of
    // expression is recognized by its own predicate.
    if (ts.isParenthesizedExpression(node))
      // Parentheses carry no meaning of their own, but the producer records
      // the type of a parenthesized expression at the span of the outermost
      // parenthesis. Unwrap, and widen the span to match, so the two agree
      // on the key. Nested parentheses widen again at each level.
      return { ...this.expr(node.expression), pos: this.span(node) };

    // A read in an enum member's initializer of a member of its enum.
    if (ts.isIdentifier(node) || ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node)) {
      const read = this.enumRead(node);
      if (read) return read;
    }

    // A `const enum` member's read is its value, which TypeScript writes in
    // its place.
    if (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node)) {
      const inlined = this.constEnumReads.get(this.span(node).join(":"));
      if (inlined !== undefined) return literalExpr(inlined, this.span(node));
    }

    // A link of an optional chain: the chain up to it is one `optional`.
    if (
      (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node) ||
        ts.isCallExpression(node) || ts.isNonNullExpression(node)) &&
      node.flags & ts.NodeFlags.OptionalChain
    )
      return this.optionalChain(node);

    if (ts.isConditionalExpression(node))
      return {
        k: "conditional",
        pos: this.span(node),
        cond: this.expr(node.condition),
        then: this.expr(node.whenTrue),
        else_: this.expr(node.whenFalse),
      };

    if (ts.isAwaitExpression(node)) return this.awaitExpr(node);

    // `void e` is `e, undefined`: the operand for its effects, then the value
    // `undefined`, a literal at the keyword.
    if (ts.isVoidExpression(node)) {
      const start = node.getStart(this.file);
      return {
        k: "comma",
        pos: this.span(node),
        left: this.expr(node.expression),
        right: { k: "lit", pos: [start, start + "void".length], lit: { a: "undefined" } },
      };
    }

    // A template without substitutions is its string; `text` is the cooked
    // value, as for a string literal.
    if (ts.isNoSubstitutionTemplateLiteral(node))
      return { k: "lit", pos: this.span(node), lit: { a: "stringlit", v: node.text } };
    if (ts.isTemplateExpression(node)) return this.template(node);

    if (ts.isIdentifier(node)) {
      if (node.text === "undefined")
        return { k: "lit", pos: this.span(node), lit: { a: "undefined" } };
      // A class is a value like any other: its construct-only code is what a
      // plain call cannot run, which its type records. Its own name in its
      // instance members, which run only once the class exists, is its class
      // binding, which they cannot capture where they are created. A static
      // initializer runs before the class value exists.
      const cls = this.classReads.get(this.span(node).join(":"));
      if (cls !== undefined && this.staticInitOf(node)?.cls === cls) this.fail(node, STATIC_INIT_CLASS);
      return { k: "id", pos: this.span(node), name: this.ownClass(node) ?? this.local(node) };
    }

    if (ts.isNewExpression(node)) {
      // `new Promise(e)`, which the overlay reads as a call of the intrinsic
      // stating the same step, read at the constructor's name. Its type
      // arguments, if written, are TypeScript's: the intrinsic's instance is
      // the producer's to propose and Lean's to check.
      const intrinsic = this.globalIntrinsics.get(this.span(node).join(":"));
      if (intrinsic)
        return this.intrinsic(intrinsic, this.span(node), this.span(node.expression),
          (node.arguments ?? []).map(a => this.expr(a)));
      // Explicit type arguments name the instantiation the producer proposes;
      // Lean validates that instantiation like any other. The callee is any
      // value; its type decides whether it has construct-only code.
      const spreads: number[] = [];
      const args = (node.arguments ?? []).map((arg, i) => {
        if (!ts.isSpreadElement(arg)) return this.expr(arg);
        spreads.push(i);
        return this.spreadOperand(arg);
      });
      return {
        k: "new",
        pos: this.span(node),
        callee: this.selfConstruction(node) ?? this.expr(node.expression),
        args,
        ...(spreads.length ? { spreads } : {}),
        ...(node.typeArguments?.length
          ? { typeArgs: node.typeArguments.map((t) => this.typeOf(t, t)) }
          : {}),
      };
    }

    if (node.kind === ts.SyntaxKind.ThisKeyword) {
      // Only an ordinary function expression, a method, or a declaration
      // stating a `this` parameter binds a receiver.
      // In sloppy code Lean admits the read where the receiver's type holds
      // objects only (`Fragment.sloppyReceiverReason`), from the function's
      // `strict` fact.
      if (this.receiverMode === null)
        this.fail(node, "`this` where no receiver is bound");
      return { k: "this", pos: this.span(node) };
    }

    if (node.kind === ts.SyntaxKind.NullKeyword)
      return { k: "lit", pos: this.span(node), lit: { a: "null" } };
    if (node.kind === ts.SyntaxKind.TrueKeyword)
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "booleanlit", v: "true" },
      };
    if (node.kind === ts.SyntaxKind.FalseKeyword)
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "booleanlit", v: "false" },
      };

    if (ts.isStringLiteral(node))
      // `text` is the DECODED value, which is what a literal type denotes.
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "stringlit", v: node.text },
      };

    // A bigint literal, negated or not, is its integer whatever its spelling.
    if (ts.isBigIntLiteral(node))
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "bigintlit", v: bigintText(node.text, false) },
      };
    if (
      ts.isPrefixUnaryExpression(node) &&
      node.operator === ts.SyntaxKind.MinusToken &&
      ts.isBigIntLiteral(node.operand)
    )
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "bigintlit", v: bigintText(node.operand.text, true) },
      };

    if (
      ts.isPrefixUnaryExpression(node) &&
      node.operator === ts.SyntaxKind.MinusToken &&
      ts.isNumericLiteral(node.operand)
    ) {
      const lexeme = numericLexeme(node.operand, this.file);
      if (lexeme === null)
        this.fail(node, "non-decimal numeric literal");
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: "-" + lexeme },
      };
    }
    // `+1` is the number `1`: unary plus returns a number operand unchanged,
    // and TypeScript types it as the literal, as it does `-1`.
    if (
      ts.isPrefixUnaryExpression(node) &&
      node.operator === ts.SyntaxKind.PlusToken &&
      ts.isNumericLiteral(node.operand) &&
      numericLexeme(node.operand, this.file) !== null
    )
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: numericLexeme(node.operand, this.file) ?? "" },
      };

    if (ts.isNumericLiteral(node)) {
      const lexeme = numericLexeme(node, this.file);
      if (lexeme === null)
        this.fail(node, "non-decimal numeric literal");
      return {
        k: "lit",
        pos: this.span(node),
        lit: { a: "numberlit", v: lexeme },
      };
    }

    if (ts.isArrowFunction(node) || ts.isFunctionExpression(node))
      return this.lambda(node);

    if (ts.isObjectLiteralExpression(node)) {
      const parts = this.objectFields(node, new Set<string>());
      const fields = parts.flatMap((p) => "spread" in p ? [] : [p]);
      if (fields.length === parts.length) return { k: "alloc", pos: this.span(node), fields };
      // Beside a spread, a key is a string: the copy's keys are compared with
      // the written ones by name.
      return { k: "build", pos: this.span(node), parts: parts.map((p) => "spread" in p ? p
        : typeof p.name === "string" ? { name: p.name, e: p.e }
        : this.fail(node, "a symbol key in an object literal with a spread is outside the fragment")) };
    }

    if (ts.isPropertyAccessExpression(node)) {
      if (node.questionDotToken)
        this.fail(node, "optional property access is outside the fragment");
      // `C.x` that TypeScript binds to a static field of class `C` reads the
      // binding its initializer bound, in a static initializer of `C`, which
      // runs before the class value exists, and the class value's own field
      // anywhere else; a static method's is the binding the class statement
      // gives it first (`classStmt`), which a static initializer may call
      // where its body does not read the class, which the model allocates only
      // after the static initializers. A
      // private static field is a binding of its own after the members.
      // A static member a base class declares is reached through the class
      // value's prototype, the base class value, which the model's class
      // value does not hold.
      if (this.inheritedStatics.has(this.span(node.name).join(":")))
        this.fail(node, "a static member read through a class that inherits it from its base is outside the fragment: " +
          "the class value reaches it through its prototype, which the model's class value does not hold");
      const cls = this.staticReads.get(this.span(node.name).join(":"));
      const init = this.staticInitOf(node);
      if (cls !== undefined && staticFieldOf(this.file, cls, node.name.text)) {
        if (init?.cls !== cls)
          return { k: "read", pos: this.span(node), field: this.memberKey(node.name), e: this.expr(node.expression) };
        if (init.closure) this.fail(node, STATIC_INIT_CLOSURE);
        return { k: "id", pos: this.span(node), name: staticName(cls, node.name.text) };
      }
      const privateStatic = this.staticPrivate(node);
      const owner = cls ?? privateStatic?.cls;
      const method = owner === undefined ? undefined : staticMethodOf(this.file, owner, node.name.text);
      if (owner !== undefined && init?.cls === owner && method &&
          (init.closure || (method.body !== undefined && this.readsClass(method.body, owner))))
        this.fail(node, STATIC_INIT_CLASS);
      if (privateStatic !== null && !method && privateStatic.cls === this.selfClass?.name)
        this.fail(node, INSTANCE_STATIC);
      if (cls !== undefined)
        return { k: "id", pos: this.span(node), name: staticName(cls, node.name.text) };
      if (privateStatic !== null) return { k: "id", pos: this.span(node), name: privateStatic.binding };
      return {
        k: "read",
        pos: this.span(node),
        field: this.memberKey(node.name),
        e: this.expr(node.expression),
      };
    }

    if (ts.isArrayLiteralExpression(node)) {
      // `[...e]` over a program's iterable is the fresh array its iterator's
      // values are collected into (`collect`).
      const [only] = node.elements;
      if (node.elements.length === 1 && only && ts.isSpreadElement(only)) {
        const kind = this.iterations.get(this.span(only.expression).join(":"));
        if (kind?.startsWith("client")) {
          if (this.hoist?.spread !== only) this.fail(only, SPREAD_POSITION);
          return this.collect(only.expression);
        }
        // Over a string, a `Set`, a `Map` or a host collection iterator, it
        // is `%Spread:K%(e)`, the fresh array of what the host's iterator
        // yields, as an argument spread's operand is (`spreadOperand`).
        if (kind) return this.spreadOperand(only);
      }
      if (node.elements.some((e) => ts.isOmittedExpression(e)))
        this.fail(node, "array literal holes are outside the fragment");
      // A spread among other elements stands for its operand's elements,
      // read where it is written, as an argument spread's operand is.
      const spreads: number[] = [];
      const elems = node.elements.map((e, i) => {
        if (!ts.isSpreadElement(e)) return this.expr(e);
        spreads.push(i);
        return this.spreadOperand(e);
      });
      return {
        k: "arrayLit",
        pos: this.span(node),
        elems,
        ...(spreads.length ? { spreads } : {}),
      };
    }

    if (ts.isElementAccessExpression(node)) {
      if (node.questionDotToken)
        this.fail(node, "optional element access is outside the fragment");
      // A `unique symbol` constant names one key: evaluating it has no
      // effect, so the read is the named read of that symbol's key.
      // `xs[k]` of an array at a `number` key is the host's read of the
      // property the number names (`%ElementAt%`, `intrinsics.mts`): the
      // object, the key, then the read, as the access evaluates them.
      // The read a `for...in` body starts with at its key is the value of
      // the entry the loop's step yielded (`forInStmt`).
      const entry = this.entryReads.get(this.span(node).join(":"));
      if (entry !== undefined)
        return { k: "index", pos: this.span(node), e: { k: "id", pos: this.span(node.expression), name: entry },
          key: { k: "lit", pos: this.span(node.argumentExpression), lit: { a: "numberlit", v: "1" } } };
      if (this.hostElements.has(this.span(node).join(":"))) {
        const bracket = node.expression.end;
        return this.intrinsic(elementAtName, this.span(node), [bracket, bracket + 1],
          [this.expr(node.expression), this.expr(node.argumentExpression)]);
      }
      const [start, end] = this.span(node.argumentExpression);
      const symbol = this.symbolKeys.get(`${start}:${end}`);
      if (symbol !== undefined)
        return {
          k: "read",
          pos: this.span(node),
          field: { symbol },
          e: this.expr(node.expression),
        };
      return {
        k: "index",
        pos: this.span(node),
        e: this.expr(node.expression),
        key: this.expr(node.argumentExpression),
      };
    }

    // `typeof e` as a value: the string naming the operand's shape. A
    // comparison of it with a shape's literal is a test (`typeofTest`).
    if (ts.isTypeOfExpression(node))
      return {
        k: "unary",
        op: "typeof",
        pos: this.span(node),
        e: this.expr(node.expression),
      };

    // A type assertion is the operand's value; the runtime never sees it.
    // What it asserts is an obligation on the operand, never a fact. `as
    // const` asserts nothing: it asks for the operand's literal types, which
    // the claims state and the checker establishes from the operand. The
    // older form `<T>e` is the same assertion as `e as T`.
    if (
      (ts.isAsExpression(node) || ts.isTypeAssertion(node)) &&
      ts.isTypeReferenceNode(node.type) &&
      ts.isIdentifier(node.type.typeName) &&
      node.type.typeName.text === "const" &&
      !node.type.typeArguments
    )
      return {
        k: "cast",
        pos: this.span(node),
        cast: "const",
        annot: null,
        e: this.expr(node.expression),
      };
    if (ts.isAsExpression(node) || ts.isTypeAssertion(node) || ts.isSatisfiesExpression(node))
      return {
        k: "cast",
        pos: this.span(node),
        cast: ts.isSatisfiesExpression(node) ? "satisfies" : "as",
        annot: this.typeOf(node.type),
        e: this.expr(node.expression),
      };
    if (ts.isNonNullExpression(node))
      return {
        k: "cast",
        pos: this.span(node),
        cast: "nonNull",
        annot: null,
        e: this.expr(node.expression),
      };

    if (ts.isPostfixUnaryExpression(node))
      return this.update(node, node.operand, node.operator, null, true);
    if (
      ts.isPrefixUnaryExpression(node) &&
      (node.operator === ts.SyntaxKind.PlusPlusToken ||
        node.operator === ts.SyntaxKind.MinusMinusToken)
    )
      return this.update(node, node.operand, node.operator, null, false);

    if (ts.isPrefixUnaryExpression(node)) {
      const unary: Record<number, UnaryOp> = {
        [ts.SyntaxKind.MinusToken]: "neg",
        [ts.SyntaxKind.PlusToken]: "plus",
        [ts.SyntaxKind.TildeToken]: "bitNot",
      };
      const op = unary[node.operator];
      if (op) return { k: "unary", pos: this.span(node), op, e: this.expr(node.operand) };
      if (node.operator !== ts.SyntaxKind.ExclamationToken)
        this.fail(node, "unary operator outside the fragment");
      return { k: "not", pos: this.span(node), e: this.expr(node.operand) };
    }

    if (ts.isBinaryExpression(node)) return this.binary(node);

    if (ts.isCallExpression(node)) {
      // `Array.isArray(e)`, which the declaration graph found to be the
      // standard library's, read through its reviewed overlay entry.
      const [tested] = node.arguments;
      if (this.globalTests.has(this.span(node).join(":")) && tested)
        return { k: "arrayTest", pos: this.span(node), e: this.expr(tested) };
      // `Promise.resolve(v)` and the like, which the overlay reads as a call
      // of the intrinsic stating the same step, read at the member's name.
      const intrinsic = this.globalIntrinsics.get(this.span(node).join(":"));
      if (intrinsic && ts.isPropertyAccessExpression(node.expression))
        return this.intrinsic(intrinsic, this.span(node), this.span(node.expression.name),
          node.arguments.map(a => this.expr(a)));
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        ts.isIdentifier(node.expression.expression) &&
        node.expression.expression.text === "Object" &&
        node.expression.name.text === "assign"
      ) {
        if (node.questionDotToken || node.expression.questionDotToken)
          this.fail(node, "an optional call of Object.assign is outside the fragment");
        // The callable form: an arrow and an object literal, at the two type
        // arguments written, or else at the two TypeScript infers.
        const callable = callableAssign(node) && (!node.typeArguments || node.typeArguments.length === 2);
        // The fragment cannot assign to Object.assign or pass Object as a value.
        // Reject any local declaration that could shadow the standard builtin.
        const checkBinding = (n: Node): void => {
          if (
            (ts.isParameterDeclaration(n) ||
              ts.isVariableDeclaration(n) ||
              ts.isFunctionDeclaration(n)) &&
            n.name &&
            ts.isIdentifier(n.name) &&
            n.name.text === "Object"
          )
            this.fail(
              n,
              "shadowing Object is outside intrinsic callable initialization",
            );
          n.forEachChild(checkBinding);
        };
        checkBinding(this.file);
        if (!callable) {
          // Copies onto a target: the target, then each source, copied as
          // it is evaluated. A spread among the arguments names sources
          // known only at run time.
          if (node.arguments.length === 0 || node.arguments.some(ts.isSpreadElement))
            this.fail(node, "Object.assign needs its target and its sources written as arguments");
          const [target, ...sources] = node.arguments;
          return {
            k: "objectAssign",
            pos: this.span(node),
            target: this.expr(target),
            sources: sources.map((a) => this.expr(a)),
          };
        }
        const initial = node.arguments[1];
        const typeArguments = node.typeArguments;
        if (!ts.isObjectLiteralExpression(initial))
          this.fail(node, "Object.assign's callable form needs an object literal");
        const inferred = typeArguments ? null : this.assignTypes.get(this.span(node).join(":"));
        if (inferred && "refused" in inferred) this.fail(node, inferred.refused);
        const [functionType, bagType] = inferred ? [inferred.functionType, inferred.bagType]
          : typeArguments?.length === 2 ? [this.typeOf(typeArguments[0]), this.typeOf(typeArguments[1])]
          : this.fail(node, "Object.assign's callable form needs its two type arguments");
        // These names either replace an intrinsic used by the lowering or
        // encounter special/non-writable properties on JavaScript functions.
        for (const property of initial.properties) {
          if (
            ts.isPropertyAssignment(property) &&
            ts.isIdentifier(property.name) &&
            [
              "call",
              "bind",
              "apply",
              "name",
              "length",
              "caller",
              "arguments",
              "__proto__",
            ].includes(property.name.text)
          )
            this.fail(
              property,
              "special function properties are outside callable initialization",
            );
        }
        return {
          k: "withValue",
          pos: this.span(node),
          fn: this.expr(node.arguments[0]),
          initial: this.expr(initial),
          functionType,
          bagType,
        };
      }
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        node.expression.name.text === "apply"
      ) {
        // Function.prototype.apply reads its list as an array-like: its
        // length, then each index in order. It never iterates the list.
        if (
          node.questionDotToken ||
          node.expression.questionDotToken ||
          node.typeArguments?.length ||
          node.arguments.length === 0 ||
          node.arguments.length > 2 ||
          node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
          !this.knownLocal(node.expression.expression)
        )
          this.refuseReceiverForm(node,
            ".apply requires a known local function, an explicit receiver and at most one argument list");
        const list = node.arguments[1];
        // A fresh array literal as the list is its elements: its allocation
        // is unobservable, and `apply` reads back exactly the values it was
        // built from, in order, so the call is the `.call` with them.
        let written: Expression | undefined = list;
        while (written && ts.isParenthesizedExpression(written)) written = written.expression;
        if (written && ts.isArrayLiteralExpression(written) &&
            !written.elements.some((e) => ts.isSpreadElement(e) || ts.isOmittedExpression(e)))
          return {
            k: "callWithReceiver",
            pos: this.span(node),
            callee: this.expr(node.expression.expression),
            receiver: this.expr(node.arguments[0]),
            args: written.elements.map((e) => this.expr(e)),
          };
        return {
          k: "applyWithReceiver",
          pos: this.span(node),
          callee: this.expr(node.expression.expression),
          receiver: this.expr(node.arguments[0]),
          list: list ? this.expr(list) : null,
        };
      }
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        ["call", "bind"].includes(node.expression.name.text)
      ) {
        if (
          node.questionDotToken ||
          node.expression.questionDotToken ||
          node.typeArguments?.length ||
          node.arguments.length === 0 ||
          node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
          !this.knownLocal(node.expression.expression)
        )
          this.refuseReceiverForm(node,
            `.${node.expression.name.text} requires a known local function, an explicit receiver and ordinary arguments`);
        return {
          k:
            node.expression.name.text === "bind"
              ? "bindWithReceiver"
              : "callWithReceiver",
          pos: this.span(node),
          callee: this.expr(node.expression.expression),
          receiver: this.expr(node.arguments[0]),
          args: node.arguments.slice(1).map((arg) => this.expr(arg)),
        };
      }
      if (node.questionDotToken)
        this.fail(node, "expected an ordinary call, not an optional one");
      // A property reference, parenthesized or not, is a call target that
      // keeps its object as the receiver (EvaluateCall). A copied method is a
      // value, and takes the `apply` form below.
      let target: Expression = node.expression;
      while (ts.isParenthesizedExpression(target)) target = target.expression;
      // `super.m(args)` calls the method the base class's prototype holds,
      // with this method's receiver: that binding's `.call(this, args)`.
      if (ts.isPropertyAccessExpression(target) && target.expression.kind === ts.SyntaxKind.SuperKeyword) {
        const binding = ts.isIdentifier(target.name) ? this.superClass?.methods.get(target.name.text) : undefined;
        if (!binding) this.fail(node, "`super.m(...)` calls a method of the base class's prototype");
        if (node.typeArguments?.length || node.arguments.some((arg) => ts.isSpreadElement(arg)))
          this.fail(node, "a `super.m(...)` call takes ordinary arguments");
        if (this.receiverMode !== "strict") this.fail(node, "`super` where no receiver is bound");
        return { k: "callWithReceiver", pos: this.span(node),
          callee: { k: "id", pos: this.span(target), name: binding },
          receiver: { k: "this", pos: this.span(target.expression) },
          args: node.arguments.map((arg) => this.expr(arg)) };
      }
      // A static method is not read from its class but bound on its own, so
      // its call is a plain call: its body reads no receiver it is given. A
      // static field is the class value's, and a call of it a method call.
      const staticOwner = ts.isPropertyAccessExpression(target) ? this.staticReads.get(this.span(target.name).join(":")) : undefined;
      const isStatic = ts.isPropertyAccessExpression(target) &&
        ((staticOwner !== undefined && !staticFieldOf(this.file, staticOwner, target.name.text)) ||
          this.staticPrivate(target) !== null);
      // A call of a static field passes the class value as its receiver,
      // which a static initializer has not yet.
      if (staticOwner !== undefined && !isStatic && this.staticInitOf(target)?.cls === staticOwner)
        this.fail(node, STATIC_INIT_CLASS);
      if (
        (ts.isPropertyAccessExpression(target) && !isStatic) ||
        ts.isElementAccessExpression(target)
      ) {
        const spreads: number[] = [];
        const args = node.arguments.map((arg, i) => {
          if (!ts.isSpreadElement(arg)) return this.expr(arg);
          spreads.push(i);
          return this.spreadOperand(arg);
        });
        // Explicit type arguments instantiate the method's leading binders;
        // Lean checks the claimed instance against them.
        const typeArgs = node.typeArguments?.map((t) => this.typeOf(t, node));
        return {
          k: "invoke",
          pos: this.span(node),
          callee: this.expr(node.expression),
          args,
          ...(spreads.length ? { spreads } : {}),
          ...(typeArgs?.length ? { typeArgs } : {}),
        };
      }
      // A spread writes the elements of one array in place of several
      // arguments, read where it is written: after every argument before it
      // and before every one after it. What it stands for — a tuple's
      // required positions, or elements a variadic callee collects — the
      // checker reads from the claims.
      const spreads: number[] = [];
      const args = node.arguments.map((arg, i) => {
        if (!ts.isSpreadElement(arg)) return this.expr(arg);
        spreads.push(i);
        return this.spreadOperand(arg);
      });
      // Explicit type arguments state the callee's instance; Lean checks the
      // claimed instance against them, as for a method call.
      const typeArgs = node.typeArguments?.map((t) => this.typeOf(t, node));
      return {
        k: "apply",
        pos: this.span(node),
        callee: this.expr(node.expression),
        args,
        ...(spreads.length ? { spreads } : {}),
        ...(typeArgs?.length ? { typeArgs } : {}),
      };
    }

    this.fail(
      node,
      `expression outside the fragment (${ts.SyntaxKind[node.kind]})`,
    );
  }

  /** An object literal's fields, in order: each property's key and value.
   * A key is its identifier, its string, or its number's `ToString`
   * (`{0: x}` owns `"0"`). A method is an ordinary function expression in a
   * field: it has no `super` or construction here, which is all that tells
   * them apart. `{ x }` is `{ x: x }`, the name read where it is written. A
   * spread of an object literal is its fields, in place: evaluated where
   * written, owning exactly those keys (DESIGN.md, "Object literals"). A
   * spread of any other value is a part of its own, copied where written
   * (DESIGN.md, "Object literals"). A key is written once: a later field
   * over an earlier one is refused, as in a literal without spreads. */
  private objectFields(node: ts.ObjectLiteralExpression, seen: Set<string>): ObjectPart[] {
    const key = (f: Node, name: Node): PropertyKey => {
      // A computed key naming a `unique symbol` constant, such as the
      // well-known `Symbol.iterator`, is that symbol's key: evaluating the
      // name has no effect, and TypeScript decides which symbol it is.
      if (ts.isComputedPropertyName(name)) {
        const symbol = this.writtenSymbol(name, f);
        if (symbol === null)
          return this.fail(f, "a computed key in an object literal other than a `unique symbol` constant is outside the fragment: an allocation's keys are the property names the literal spells, and a key computed at run time is none of them");
        const text = `[symbol ${symbol}]`;
        if (seen.has(text)) this.fail(f, "duplicate field name in a record");
        seen.add(text);
        return { symbol };
      }
      const text = ts.isIdentifier(name) || ts.isStringLiteral(name) ? name.text
        : ts.isNumericLiteral(name) ? numericKey(name.text)
        : this.fail(f, "expected a plain property name");
      if (seen.has(text)) this.fail(f, "duplicate field name in a record");
      if (text === "__proto__") this.fail(f, "prototype initializers are outside the fragment");
      if (text === "then") this.fail(f, FORGED_PROMISE);
      seen.add(text);
      return text;
    };
    return node.properties.flatMap((f) => {
      if (ts.isMethodDeclaration(f)) return [{ name: key(f, f.name), e: this.lambda(f) }];
      if (ts.isShorthandPropertyAssignment(f) && !f.objectAssignmentInitializer && ts.isIdentifier(f.name))
        return [{ name: key(f, f.name), e: this.expr(f.name) }];
      if (ts.isPropertyAssignment(f)) return [{ name: key(f, f.name), e: this.expr(f.initializer) }];
      if (ts.isSpreadAssignment(f)) {
        let operand: Expression = f.expression;
        while (ts.isParenthesizedExpression(operand)) operand = operand.expression;
        if (ts.isObjectLiteralExpression(operand)) return this.objectFields(operand, seen);
        // A spread of a value copies its own enumerable properties when it
        // is evaluated; which it has is its type's to say, and Lean's.
        return [{ spread: this.expr(f.expression) }];
      }
      if (ts.isGetAccessorDeclaration(f) || ts.isSetAccessorDeclaration(f))
        return this.fail(f, "an accessor runs code where its property is read or written; the heap model has data properties only");
      return this.fail(f, "expected a plain property; no accessors, methods or spreads");
    });
  }

  /** An optional chain: `r?.x` evaluates `r` once and is `undefined` where it
   * is null or undefined, else the rest of the chain on its value, which the
   * body reads as the variable `CHAIN` at the `?.` token. A link after the
   * chain's `?.` (`.c` in `r?.b.c`) extends the body, so it is skipped with
   * the rest; a second `?.` tests the chain so far, whose `undefined` it
   * passes on, as JavaScript's short-circuit does. The body's nodes span from
   * the `?.` token, so each has a claim site of its own. On a `null` or
   * `undefined` literal the chain is that literal, then `undefined`: its
   * body never runs. */
  private optionalChain(
    node: ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression,
  ): Expr {
    const question = ts.isNonNullExpression(node) ? undefined : node.questionDotToken;
    if (question) {
      const at = this.span(question);
      const receiver = this.expr(node.expression);
      if (receiver.k === "lit" && (receiver.lit.a === "null" || receiver.lit.a === "undefined"))
        return { k: "comma", pos: this.span(node), left: receiver, right: { k: "lit", pos: at, lit: { a: "undefined" } } };
      const saved: Expr = { k: "id", pos: at, name: CHAIN };
      return { k: "optional", pos: this.span(node), at, receiver, body: this.chainLink(node, saved, [at[0], node.end]) };
    }
    const chain = this.expr(node.expression);
    if (chain.k === "comma") return { ...chain, pos: this.span(node) };
    if (chain.k !== "optional") this.fail(node, "a link of an optional chain without its `?.`");
    return { ...chain, pos: this.span(node), body: this.chainLink(node, chain.body, [chain.at[0], node.end]) };
  }

  /** One link of an optional chain applied to `object`, the chain so far. */
  private chainLink(
    node: ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression,
    object: Expr,
    pos: Span,
  ): Expr {
    if (ts.isNonNullExpression(node)) return { k: "cast", pos, cast: "nonNull", annot: null, e: object };
    if (ts.isPropertyAccessExpression(node)) {
      if (this.staticReads.has(this.span(node.name).join(":")) || this.staticPrivate(node) !== null)
        this.fail(node, "an optional read of a static member is outside the fragment");
      return { k: "read", pos, field: this.memberKey(node.name), e: object };
    }
    if (ts.isElementAccessExpression(node)) {
      const [start, end] = this.span(node.argumentExpression);
      const symbol = this.symbolKeys.get(`${start}:${end}`);
      if (symbol !== undefined) return { k: "read", pos, field: { symbol }, e: object };
      return { k: "index", pos, e: object, key: this.expr(node.argumentExpression) };
    }
    let target: Expression = node.expression;
    while (ts.isParenthesizedExpression(target)) target = target.expression;
    // `o.m?.()` tests the method, but calls it with `o` as its receiver: the
    // chain would have to save the object apart from the tested value.
    if (node.questionDotToken && (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)))
      this.fail(node, "an optional call of a method is outside the fragment");
    const spreads: number[] = [];
    const args = node.arguments.map((arg, i) => {
      if (!ts.isSpreadElement(arg)) return this.expr(arg);
      spreads.push(i);
      return this.spreadOperand(arg);
    });
    const method = !node.questionDotToken && (object.k === "read" || object.k === "index");
    const typeArgs = node.typeArguments?.map((t) => this.typeOf(t, node));
    if (typeArgs?.length && !method)
      this.fail(node, "explicit type arguments are admitted on a method call only");
    return {
      k: method ? "invoke" : "apply",
      pos,
      callee: object,
      args,
      ...(spreads.length ? { spreads } : {}),
      ...(method && typeArgs?.length ? { typeArgs } : {}),
    };
  }

  // A call signature alone does not establish the inherited .call intrinsic.
  // Follow immutable lexical aliases to source-created functions, and to a
  // function-valued member of a `const` object literal whose member no write
  // in the file can replace. Parameters and arbitrary call results may carry
  // their own .call property, so are refused.
  /** `f.call(r, …)`, `.apply` or `.bind` of what is no known local
   * function. Of a method TypeScript resolves the member to, the form passes
   * it a receiver other than its host, where a method's contract is relative
   * to its host: extraction, refused by that reason. */
  private refuseReceiverForm(node: ts.CallExpression, refusal: string): never {
    const form = ts.isPropertyAccessExpression(node.expression) ? node.expression.name.text : "call";
    let target: Expression = ts.isPropertyAccessExpression(node.expression) ? node.expression.expression : node.expression;
    while (ts.isParenthesizedExpression(target)) target = target.expression;
    if (ts.isPropertyAccessExpression(target) && this.methodTargets.has(this.span(target.name).join(":")))
      this.fail(node, `a method read off its object is not a function value: \`.${form}\` passes it a receiver ` +
        "other than the object it is read from, and a method's contract is relative to that object " +
        "(DESIGN.md, \"Method members are host-relative\")");
    this.fail(node, refusal);
  }

  /** `localArrow`, and every local it follows is confined: code that may
   * hold the local's value cannot have replaced the member or added an own
   * `call`, `apply` or `bind`. */
  private knownLocal(node: Expression): boolean {
    const seen = new Set<number>();
    const followed = new Set<string>();
    const functions = new Set<Node>();
    return this.localArrow(node, seen, followed, functions) && this.confined(seen, followed, functions);
  }

  private bindings?: Map<Node, Map<string, Node>>;
  /** The declaration a name resolves to, lexically: the nearest scope
   * enclosing the reference that binds it (`bindingScope`), a parameter
   * before a named function expression's own name; none for a global. */
  private resolve(id: Identifier): Node | undefined {
    if (!this.bindings) {
      const bindings = new Map<Node, Map<string, Node>>();
      const visit = (n: Node): void => {
        if (ts.isTypeNode(n) || ts.isInterfaceDeclaration(n) || ts.isTypeAliasDeclaration(n)) return;
        const name = nameOf(n);
        if ((ts.isParameterDeclaration(n) || ts.isVariableDeclaration(n) || ts.isBindingElement(n) ||
             ts.isFunctionDeclaration(n) || ts.isClassDeclaration(n) || ts.isEnumDeclaration(n) ||
             ts.isFunctionExpression(n) || ts.isClassExpression(n) || ts.isImportSpecifier(n) ||
             ts.isNamespaceImport(n) || ts.isImportClause(n)) && name && ts.isIdentifier(name)) {
          const scope = ts.isImportSpecifier(n) || ts.isNamespaceImport(n) || ts.isImportClause(n)
            ? this.file : bindingScope(n);
          const own = ts.isFunctionExpression(n) || ts.isClassExpression(n);
          const names = bindings.get(scope) ?? new Map<string, Node>();
          bindings.set(scope, names);
          const before = names.get(name.text);
          if (!before || (!own && (ts.isFunctionExpression(before) || ts.isClassExpression(before))))
            names.set(name.text, n);
        }
        n.forEachChild(visit);
      };
      visit(this.file);
      this.bindings = bindings;
    }
    for (let at: Node | undefined = id.parent; at; at = at.parent) {
      const found = this.bindings.get(at)?.get(id.text);
      if (found) return found;
    }
    return undefined;
  }

  /** Whether the values followed are confined: code holding one is the
   * file's own, whose writes `memberMayBeWritten` reads. Every reference to
   * a local declared at `seen`, or to one of the file's function
   * declarations in `functions` (a reference resolved to it, `resolve`), is
   * the callee of a call, the object of `.call`, `.apply` or `.bind`
   * (directly or through a member), the target of a plain assignment to it,
   * the object of a read or write, not a call, of a member other than
   * `call`, `apply`, `bind` and the members `followed`, or a local's value: a
   * local's initializer or the right side of a plain assignment to it, the
   * reference itself, or a spread or member value in an object literal that
   * is. Such a local is confined in turn, and the member it is given at is
   * followed. Any other reference (an argument, `Object.assign`'s target, a
   * method call's receiver, a return, a read of a followed member) may hand
   * the value to code that replaces its member or adds a `call` of its own.
   * An object literal a local holds has no accessor: a spread of it runs its
   * getters with the object as receiver. */
  private confined(seen: Set<number>, followed: Set<string>, functions: Set<Node>): boolean {
    const targets = new Set<Node>(functions);
    const declared = new Map<number, ts.VariableDeclaration>();
    const collect = (n: Node): void => {
      if (ts.isVariableDeclaration(n)) declared.set(n.getStart(this.file), n);
      n.forEachChild(collect);
    };
    collect(this.file);
    for (const start of seen) {
      const decl = declared.get(start);
      if (decl) targets.add(decl);
    }
    const strip = (n: Node): Node => {
      let at = n;
      while (ts.isParenthesizedExpression(at.parent)) at = at.parent;
      return at;
    };
    const hasAccessor = (literal: Node): boolean => ts.isObjectLiteralExpression(literal) &&
      literal.properties.some((p) => ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p));
    // The local whose value `value` is: its initializer, or the right side
    // of a plain assignment to it.
    const holderOf = (value: Node): Node | undefined => {
      const at = strip(value);
      const holder = at.parent;
      if (ts.isVariableDeclaration(holder) && holder.initializer === at) return holder;
      if (ts.isBinaryExpression(holder) && holder.right === at &&
          holder.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        let left: Expression = holder.left;
        while (ts.isParenthesizedExpression(left)) left = left.expression;
        const target = ts.isIdentifier(left) ? this.resolve(left) : undefined;
        return target && ts.isVariableDeclaration(target) ? target : undefined;
      }
      return undefined;
    };
    const gateCallee = (access: Node): boolean => {
      if (!ts.isPropertyAccessExpression(access) || !["call", "apply", "bind"].includes(access.name.text))
        return false;
      const call = strip(access).parent;
      return ts.isCallExpression(call) && call.expression === strip(access);
    };
    const allowed = (n: Identifier): boolean => {
      const at = strip(n);
      const parent = at.parent;
      if (ts.isCallExpression(parent) && parent.expression === at) return true;
      if (ts.isPropertyAccessExpression(parent) && parent.expression === at) {
        if (gateCallee(parent)) return true;
        const outer = strip(parent).parent;
        if (ts.isPropertyAccessExpression(outer) && outer.expression === strip(parent) && gateCallee(outer))
          return true;
        // Another member, read or written, not called: its value is not one
        // followed, and the object is not handed on.
        const key = parent.name.text;
        return !followed.has(key) && !["call", "apply", "bind"].includes(key) &&
          !((ts.isCallExpression(outer) || ts.isNewExpression(outer)) && outer.expression === strip(parent)) &&
          !ts.isTaggedTemplateExpression(outer);
      }
      if (ts.isBinaryExpression(parent) && parent.left === at &&
          parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) return true;
      let value: Node = at;
      if (ts.isSpreadAssignment(parent) || ts.isShorthandPropertyAssignment(parent) ||
          (ts.isPropertyAssignment(parent) && parent.initializer === at)) {
        if (!ts.isSpreadAssignment(parent)) {
          if (!ts.isIdentifier(parent.name)) return false;
          followed.add(parent.name.text);
        }
        value = parent.parent;
      }
      const holder = holderOf(value);
      if (!holder || hasAccessor(value)) return false;
      targets.add(holder);
      return true;
    };
    // A declaration's own name, or a member's: no reference.
    const isName = (n: Identifier): boolean => {
      const parent = n.parent;
      return (ts.isPropertyAccessExpression(parent) && parent.name === n) ||
        (ts.isQualifiedName(parent) && parent.right === n) ||
        ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
          ts.isPropertyDeclaration(parent) || ts.isGetAccessorDeclaration(parent) ||
          ts.isSetAccessorDeclaration(parent) || ts.isVariableDeclaration(parent) ||
          ts.isParameterDeclaration(parent) || ts.isBindingElement(parent) ||
          ts.isFunctionDeclaration(parent) || ts.isFunctionExpression(parent) ||
          ts.isClassDeclaration(parent) || ts.isClassExpression(parent)) && nameOf(parent) === n);
    };
    // A local or member followed late may have been referenced before:
    // repeat until neither grows.
    for (let size = -1; size !== targets.size + followed.size;) {
      size = targets.size + followed.size;
      let ok = true;
      const visit = (n: Node): void => {
        // A type names no value.
        if (!ok || ts.isTypeNode(n)) return;
        if (ts.isIdentifier(n) && !isName(n)) {
          const target = this.resolve(n);
          if (target && targets.has(target) && !allowed(n)) ok = false;
        }
        n.forEachChild(visit);
      };
      visit(this.file);
      if (!ok) return false;
      for (const target of targets)
        if (ts.isVariableDeclaration(target) &&
            (!ts.isIdentifier(target.name) || (target.initializer && hasAccessor(target.initializer))))
          return false;
    }
    return true;
  }

  private localArrow(node: Expression, seen = new Set<number>(), followed = new Set<string>(),
      functions = new Set<Node>()): boolean {
    if (ts.isParenthesizedExpression(node))
      return this.localArrow(node.expression, seen, followed, functions);
    if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return true;
    if (
      ts.isPropertyAccessExpression(node) &&
      !node.questionDotToken &&
      ts.isIdentifier(node.expression)
    ) {
      // A member of a local every value of which is an object literal that
      // gives the member a known function, which no write in the file can
      // replace.
      const member = node.name.text;
      if (this.memberMayBeWritten(member)) return false;
      followed.add(member);
      const values = this.localValues(node.expression, seen);
      return !!values && values.every((v) => this.memberOf(v, member, seen, followed, functions) === true);
    }
    if (
      ts.isCallExpression(node) &&
      ts.isPropertyAccessExpression(node.expression) &&
      ts.isIdentifier(node.expression.expression) &&
      node.expression.expression.text === "Object" &&
      node.expression.name.text === "assign"
    )
      // Its initializer is separately parsed through the full Object.assign
      // gate. Do not parse it again here: its body may refer back to this name.
      return (
        node.arguments.length === 2 &&
        ts.isArrowFunction(node.arguments[0]) &&
        ts.isObjectLiteralExpression(node.arguments[1])
      );
    if (
      ts.isCallExpression(node) &&
      ts.isPropertyAccessExpression(node.expression) &&
      node.expression.name.text === "bind"
    )
      return this.localArrow(node.expression.expression, seen, followed, functions);
    if (!ts.isIdentifier(node)) return false;
    const values = this.localValues(node, seen);
    if (values) return values.every((v) => this.localArrow(v, seen, followed, functions));
    const declaration = this.resolve(node);
    if (!declaration || !this.moduleFunction(node)) return false;
    functions.add(declaration);
    return true;
  }

  /** What the object literal `value` holds at `member` once built: `true`
   * where the last of its parts giving the key gives a known local function
   * (a method, or a value `localArrow` admits), `"absent"` where no part
   * gives it, `false` where that is not known. A spread gives the key where
   * its source does: a local every value of which is an object literal, or a
   * literal; it copies the own enumerable data properties, which a literal's
   * members are. */
  private memberOf(value: Expression, member: string, seen: Set<number>,
      followed: Set<string>, functions: Set<Node>): boolean | "absent" {
    while (ts.isParenthesizedExpression(value)) value = value.expression;
    if (!ts.isObjectLiteralExpression(value)) return false;
    let found: boolean | "absent" = "absent";
    for (const p of value.properties) {
      if (ts.isSpreadAssignment(p)) {
        let source = p.expression;
        while (ts.isParenthesizedExpression(source)) source = source.expression;
        const sources = ts.isIdentifier(source) ? this.localValues(source, seen)
          : ts.isObjectLiteralExpression(source) ? [source] : undefined;
        if (!sources) return false;
        const parts = sources.map((s) => this.memberOf(s, member, seen, followed, functions));
        if (parts.every((x) => x === "absent")) continue;
        // A source that may lack the key leaves the earlier part's value.
        found = parts.every((x) => x === true || (x === "absent" && found === true));
        continue;
      }
      if (!p.name || ts.isComputedPropertyName(p.name) || ts.isPrivateIdentifier(p.name)) return false;
      if (p.name.text !== member) continue;
      found = ts.isMethodDeclaration(p) ? true
        : ts.isPropertyAssignment(p) ? this.localArrow(p.initializer, seen, followed, functions)
        : ts.isShorthandPropertyAssignment(p) ? this.localArrow(p.name, seen, followed, functions)
        : false;
    }
    return found;
  }

  /** Whether this identifier resolves to one of the file's function
   * declarations with a body, not exported: an exported one is held by
   * every importer, where other code may give it an own `call`. A script's
   * top-level function is also a property of the global object, which, by
   * the trusted assumption that only the file writes its top-level
   * bindings, no other code writes (DESIGN, Trust surface). No write in the
   * file can replace the `call`, `apply` or `bind` its object inherits (an
   * assignment to the declaration's binding is refused where it is
   * written). */
  private moduleFunction(node: Identifier): boolean {
    const declaration = this.resolve(node);
    if (!declaration || !ts.isFunctionDeclaration(declaration) || !declaration.parent ||
        !ts.isSourceFile(declaration.parent))
      return false;
    const declared = this.file.statements.filter((s) => {
      const name = nameOf(s);
      return !!name && ts.isIdentifier(name) && name.text === node.text &&
        !ts.isInterfaceDeclaration(s) && !ts.isTypeAliasDeclaration(s);
    });
    return declared.every((s) => ts.isFunctionDeclaration(s) && !!s.body &&
        !s.modifiers?.some((m) => m.kind === ts.SyntaxKind.DeclareKeyword || m.kind === ts.SyntaxKind.ExportKeyword)) &&
      !["call", "apply", "bind"].some((member) => this.memberMayBeWritten(member));
  }

  /** Whether any assignment in the file may replace a member of this name: a
   * write to it by name, or to a computed key that is not another name. */
  private memberMayBeWritten(member: string): boolean {
    let found = false;
    const visit = (n: Node): void => {
      if (found) return;
      if (
        ts.isBinaryExpression(n) &&
        n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment
      ) {
        let target: Expression = n.left;
        while (ts.isParenthesizedExpression(target)) target = target.expression;
        if (
          ts.isPropertyAccessExpression(target) &&
          target.name.text === member
        )
          found = true;
        if (
          ts.isElementAccessExpression(target) &&
          !(
            ts.isStringLiteral(target.argumentExpression) &&
            target.argumentExpression.text !== member
          )
        )
          found = true;
      }
      n.forEachChild(visit);
    };
    visit(this.file);
    return found;
  }

  /** Every value the local this identifier names may hold, lexically: a
   * `const`'s initializer; a `let`'s initializer and the right side of each
   * plain assignment to it in its block, the only places a write to it can
   * be. None where it names a parameter, something declared elsewhere, or a
   * `let` that is written otherwise (a compound assignment, an update, a
   * pattern, a loop head) or whose name a declaration inside its block
   * shadows. */
  private localValues(
    node: Identifier,
    seen: Set<number>,
  ): Expression[] | undefined {
    const decl = this.resolve(node);
    if (!decl || !ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name) || !decl.initializer)
      return undefined;
    const list = decl.parent;
    const statement = list?.parent;
    if (!list || ts.isCatchClause(list) || !statement || !ts.isVariableStatement(statement) ||
        !statement.parent || !ts.isBlock(statement.parent))
      return undefined;
    if (seen.has(decl.getStart(this.file))) return undefined;
    seen.add(decl.getStart(this.file));
    if (list.flags & ts.NodeFlags.Const) return [decl.initializer];
    if (!(list.flags & ts.NodeFlags.Let)) return undefined;
    return this.letWrites(statement.parent, decl.name);
  }

  /** The values the `let` declared at `declared` in `block` is given: its
   * initializer and each plain assignment's right side; none where another
   * form writes it or a declaration in the block shadows it. */
  private letWrites(block: ts.Block, declared: Identifier): Expression[] | undefined {
    const name = declared.text;
    const values: Expression[] = [];
    let unknown = false;
    const outermost = (n: Node): Node => {
      let at = n;
      while (ts.isParenthesizedExpression(at.parent) || ts.isArrayLiteralExpression(at.parent) ||
          ts.isObjectLiteralExpression(at.parent) || ts.isSpreadElement(at.parent) ||
          ts.isSpreadAssignment(at.parent) || ts.isPropertyAssignment(at.parent) ||
          ts.isShorthandPropertyAssignment(at.parent))
        at = at.parent;
      return at;
    };
    const visit = (n: Node): void => {
      if (unknown) return;
      // Another declaration of the name inside the block: refused rather
      // than resolved.
      const declaredName = n === declared.parent ? undefined
        : ts.isVariableDeclaration(n) || ts.isParameterDeclaration(n) || ts.isBindingElement(n) ||
          ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) ||
          ts.isClassDeclaration(n) || ts.isClassExpression(n) ? n.name : undefined;
      if (declaredName && ts.isIdentifier(declaredName) && declaredName.text === name) {
        unknown = true;
        return;
      }
      if (ts.isIdentifier(n) && n !== declared && n.text === name) {
        const parent = n.parent;
        if (ts.isPropertyAccessExpression(parent) && parent.name === n) return;
        if ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent)) && parent.name === n) return;
        const top = outermost(n);
        const holder = top.parent;
        if (ts.isBinaryExpression(holder) && holder.left === top &&
            holder.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
            holder.operatorToken.kind <= ts.SyntaxKind.LastAssignment) {
          if (outermostIs(top, n) && holder.operatorToken.kind === ts.SyntaxKind.EqualsToken)
            values.push(holder.right);
          else unknown = true;
        } else if ((ts.isPrefixUnaryExpression(holder) || ts.isPostfixUnaryExpression(holder)) &&
            (holder.operator === ts.SyntaxKind.PlusPlusToken || holder.operator === ts.SyntaxKind.MinusMinusToken)) {
          unknown = true;
        } else if ((ts.isForOfStatement(holder) || ts.isForInStatement(holder)) && holder.initializer === top) {
          unknown = true;
        }
      }
      n.forEachChild(visit);
    };
    const outermostIs = (top: Node, n: Node): boolean => {
      let at: Node = top;
      while (ts.isParenthesizedExpression(at)) at = at.expression;
      return at === n;
    };
    const decl = declared.parent;
    if (!ts.isVariableDeclaration(decl) || !decl.initializer) return undefined;
    values.push(decl.initializer);
    visit(block);
    return unknown ? undefined : values;
  }

  /** A compound assignment or an increment: the target's parts are evaluated
   * once, so the verifier is handed one form rather than a rewrite that would
   * evaluate an effectful key twice. */
  private update(
    node: Expression,
    target: Expression,
    token: ts.SyntaxKind,
    rhs: Expression | null,
    post: boolean,
  ): Expr {
    const ops: Record<number, ArithOp> = {
      [ts.SyntaxKind.PlusEqualsToken]: "add",
      [ts.SyntaxKind.MinusEqualsToken]: "sub",
      [ts.SyntaxKind.AsteriskEqualsToken]: "mul",
      [ts.SyntaxKind.SlashEqualsToken]: "div",
      [ts.SyntaxKind.AsteriskAsteriskEqualsToken]: "pow",
      [ts.SyntaxKind.PercentEqualsToken]: "rem",
      [ts.SyntaxKind.PlusPlusToken]: "add",
      [ts.SyntaxKind.MinusMinusToken]: "sub",
    };
    const op = ops[token];
    if (!op)
      this.fail(
        node,
        `binary operator outside the fragment (${ts.tokenToString(token)})`,
      );
    const lhs = this.expr(target);
    if (lhs.k !== "id" && lhs.k !== "read" && lhs.k !== "index")
      this.fail(target, "only field and local assignments are supported");
    return {
      k: "update",
      pos: this.span(node),
      op,
      target: lhs,
      rhs: rhs ? this.expr(rhs) : null,
      post,
    };
  }

  /** A template literal is the concatenation of its parts, in order:
   * `` `h${a}m${b}t` `` is `(((("h" + a) + "m") + b) + "t")`, which converts
   * each substitution by `ToString` where the template does, after the ones
   * before it; the first part, a string, makes every `+` a concatenation.
   * Each partial concatenation spans from the template's start to the end of
   * its last part, so every node has a span of its own and the whole has the
   * template's. */
  private template(node: ts.TemplateExpression): Expr {
    const start = node.getStart(this.file);
    let acc: Expr = { k: "lit", pos: this.span(node.head), lit: { a: "stringlit", v: node.head.text } };
    for (const part of node.templateSpans) {
      acc = { k: "arith", pos: [start, part.expression.end], op: "add", l: acc, r: this.expr(part.expression) };
      acc = {
        k: "arith",
        pos: [start, part.literal.end],
        op: "add",
        l: acc,
        r: { k: "lit", pos: this.span(part.literal), lit: { a: "stringlit", v: part.literal.text } },
      };
    }
    return acc;
  }

  /** Whether an `instanceof` right operand names a class of this file that
   * declares or inherits, from a class of this file, a static
   * `[Symbol.hasInstance]`. Syntactic: it only chooses a refusal's reason. */
  private hasInstanceClass(right: Expression): boolean {
    return this.hasInstanceAlong(ts.isIdentifier(right) ? right.text : undefined) !== null;
  }

  /** The class, of those the file declares at its top level, along `name`'s
   * chain of bases whose static `[Symbol.hasInstance]` method `instanceof`
   * of `name` calls: the nearest declaring one, which a derived class
   * inherits through its constructor's prototype chain. Syntactic up to the
   * key, which `staticHasInstance` resolves. */
  private hasInstanceAlong(name: string | undefined): { cls: string; member: ts.MethodDeclaration } | null {
    const classes = new Map<string, ClassDeclaration>();
    for (const s of this.file.statements)
      if (ts.isClassDeclaration(s) && s.name) classes.set(s.name.text, s);
    const seen = new Set<string>();
    while (name && !seen.has(name)) {
      seen.add(name);
      const c = classes.get(name);
      if (!c) return null;
      const member = c.members.find((m): m is ts.MethodDeclaration => ts.isMethodDeclaration(m) &&
        ts.isComputedPropertyName(m.name) && !!m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword) &&
        m.name.expression.getText(this.file) === "Symbol.hasInstance");
      if (member) return { cls: name, member };
      const base = c.heritageClauses?.find((h) => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression;
      name = base && ts.isIdentifier(base) ? base.text : undefined;
    }
    return null;
  }

  /** Whether a class member's computed key is the built-in well-known
   * `Symbol.hasInstance`: TypeScript binds it to the standard library's
   * `unique symbol` property of that name (`symbolKeys`). */
  private staticHasInstance(name: ts.PropertyName): boolean {
    if (!ts.isComputedPropertyName(name) || !ts.isPropertyAccessExpression(name.expression)) return false;
    const symbol = this.symbolKeys.get(this.span(name.expression).join(":"));
    const identity = symbol === undefined ? undefined : this.symbolIdentities[symbol];
    return !!identity && identity.module.startsWith("typescript/lib/") && identity.name === "hasInstance";
  }

  private binary(node: BinaryExpression): Expr {
    if (node.operatorToken.kind === ts.SyntaxKind.CommaToken)
      return { k: "comma", pos: this.span(node), left: this.expr(node.left), right: this.expr(node.right) };
    // `e instanceof Array`, which the declaration graph found to name the
    // standard library's global: the same test as `Array.isArray(e)`.
    if (node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword &&
        this.globalTests.has(this.span(node).join(":")))
      return { k: "arrayTest", pos: this.span(node), e: this.expr(node.left) };
    // Any other `instanceof` looks for a constructor's prototype along the
    // operand's prototype chain, or calls the constructor's static
    // `[Symbol.hasInstance]`. For a class of this file, which TypeScript binds
    // the right operand to, it evaluates the operand, then reads the class's
    // prototype object, and looks for the key only that object owns along
    // the operand's chain (DESIGN.md, "Guards").
    if (node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) {
      const cls = this.classTests.get(this.span(node.right).join(":"));
      // A class whose chain of constructors holds a static
      // `[Symbol.hasInstance]`: `instanceof` calls that method with the
      // operand and converts its result by `ToBoolean` (ECMA-262,
      // InstanceofOperator), walking no prototype chain. The method reads no
      // `this` (`classBody`), so its receiver, the class, is unobservable,
      // and it is the static binding a plain call reads. Its answer says
      // nothing of the operand's type, so the test narrows nothing.
      const custom = cls ? this.hasInstanceAlong(cls) : null;
      if (custom && this.staticHasInstance(custom.member.name)) {
        const keyword = node.operatorToken.getStart(this.file);
        const callee: Expr = { k: "id", pos: this.span(node.right), name: staticName(custom.cls, HAS_INSTANCE) };
        const call: Expr = { k: "apply", pos: [node.getStart(this.file), node.operatorToken.end], callee,
          args: [this.expr(node.left)] };
        return { k: "not", pos: this.span(node),
          e: { k: "not", pos: [keyword, keyword + "instanceof".length], e: call } };
      }
      if (this.hasInstanceClass(node.right))
        this.fail(node, "`instanceof` of a class with a static `[Symbol.hasInstance]` calls that method, a computed static member, outside the fragment");
      // A right operand whose type states `[Symbol.hasInstance]`:
      // `instanceof` reads that method off it and calls it with the operand,
      // the right operand its receiver, converting the result by
      // `ToBoolean` (ECMA-262, InstanceofOperator). The operands are names,
      // whose reads JavaScript's order and the call's alike leave unchanged.
      if (!cls && this.hookTests.has(this.span(node.right).join(":"))) {
        const symbol = this.symbolIdentities.findIndex((s) =>
          s.module.startsWith("typescript/lib/") && s.name === "hasInstance");
        if (!ts.isIdentifier(node.left) || symbol < 0)
          this.fail(node, "`instanceof` of a value whose type states `[Symbol.hasInstance]` calls it: its left operand is a name");
        const start = node.getStart(this.file);
        const keyword = node.operatorToken.getStart(this.file);
        const keywordEnd = node.operatorToken.end;
        const call: Expr = { k: "invoke", pos: [start, keywordEnd],
          callee: { k: "read", pos: [keyword, node.end], field: { symbol }, e: this.expr(node.right) },
          args: [this.expr(node.left)] };
        return { k: "not", pos: this.span(node), e: { k: "not", pos: [keyword, keywordEnd], e: call } };
      }
      if (!cls)
        this.fail(node, "`instanceof` whose right operand is not a class declared at the file's top level: nothing in the file says which prototype a constructor from elsewhere gives its instances");
      return { k: "instanceTest", pos: this.span(node), e: this.expr(node.left),
        proto: { k: "id", pos: this.span(node.right), name: this.ownClass(node.right) ?? prototypeName(cls) },
        key: classKey(cls) };
    }
    // `key in o`: whether `o` has the key, its own or an inherited one.
    // Which keys and operands the model answers as JavaScript does is Lean's
    // to decide (`inKeyRefusal`, `inOperand`, `inKeyList`).
    if (node.operatorToken.kind === ts.SyntaxKind.InKeyword) {
      const key = inKey(node);
      // A key TypeScript types as other than string literals (a number, an
      // array index among them, a symbol, a string known only at run time)
      // names what the model does not answer as JavaScript does: the test is
      // the host's `%HasProperty%(k, o)`, a Boolean that narrows nothing
      // (`intrinsics.mts`), evaluated as `in` evaluates: the key, the object,
      // then the lookup.
      if (this.hostIns.has(this.span(key).join(":"))) {
        const keyword = node.operatorToken.getStart(this.file);
        return this.intrinsic(hasPropertyName, this.span(node), [keyword, keyword + "in".length],
          [this.expr(node.left), this.expr(node.right)]);
      }
      // `#x in o` asks whether `o` itself holds the slot, as its class's
      // construction installs it; the model's key test walks the prototype
      // chain, and would find an instance's slot from an object inheriting
      // from it.
      if (ts.isPrivateIdentifier(key))
        this.fail(node.left, "`#x in o` tests an object's own private slot, where the model's key test walks the prototype chain");
      return { k: "inTest", pos: this.span(node), key: this.expr(node.left), e: this.expr(node.right) };
    }
    switch (node.operatorToken.kind) {
      case ts.SyntaxKind.PlusEqualsToken:
      case ts.SyntaxKind.MinusEqualsToken:
      case ts.SyntaxKind.AsteriskEqualsToken:
      case ts.SyntaxKind.SlashEqualsToken:
      case ts.SyntaxKind.AsteriskAsteriskEqualsToken:
      case ts.SyntaxKind.PercentEqualsToken:
        return this.update(
          node,
          node.left,
          node.operatorToken.kind,
          node.right,
          false,
        );
    }
    const arithmetic: Record<number, BinaryOp> = {
      [ts.SyntaxKind.PlusToken]: "add",
      [ts.SyntaxKind.MinusToken]: "sub",
      [ts.SyntaxKind.AsteriskToken]: "mul",
      [ts.SyntaxKind.SlashToken]: "div",
      [ts.SyntaxKind.AsteriskAsteriskToken]: "pow",
      [ts.SyntaxKind.PercentToken]: "rem",
      [ts.SyntaxKind.LessThanToken]: "lt",
      [ts.SyntaxKind.LessThanEqualsToken]: "le",
      [ts.SyntaxKind.GreaterThanToken]: "gt",
      [ts.SyntaxKind.GreaterThanEqualsToken]: "ge",
    };
    const arith = arithmetic[node.operatorToken.kind];
    if (arith)
      return {
        k: "arith",
        pos: this.span(node),
        op: arith,
        l: this.expr(node.left),
        r: this.expr(node.right),
      };
    const logical: Record<number, "nullish" | "or" | "and"> = {
      [ts.SyntaxKind.QuestionQuestionEqualsToken]: "nullish",
      [ts.SyntaxKind.BarBarEqualsToken]: "or",
      [ts.SyntaxKind.AmpersandAmpersandEqualsToken]: "and",
    };
    const logicalOp = logical[node.operatorToken.kind];
    if (logicalOp && (logicalOp !== "nullish" || !ts.isIdentifier(node.left))) {
      const target = this.expr(node.left);
      if (target.k !== "id" && target.k !== "read" && target.k !== "index")
        this.fail(node.left, "only field and local assignments are supported");
      if (target.k === "id" && target.name === "undefined")
        this.fail(node.left, "shadowing undefined is outside the fragment");
      return {
        k: "logicalAssign",
        pos: this.span(node),
        op: logicalOp,
        target,
        rhs: this.expr(node.right),
      };
    }
    if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionEqualsToken) {
      if (!ts.isIdentifier(node.left) || node.left.text === "undefined")
        this.fail(node.left, "nullish assignment requires a local identifier");
      return {
        k: "nullishAssign",
        pos: this.span(node),
        name: this.local(node.left),
        namePos: this.span(node.left),
        rhs: this.expr(node.right),
      };
    }
    if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken)
      return {
        k: "coalesce",
        pos: this.span(node),
        left: this.expr(node.left),
        right: this.expr(node.right),
      };
    if (
      node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
      ts.isArrayLiteralExpression(node.left)
    ) {
      // `[a, b = d, ...r] = rhs`: each element names a mutable local or a
      // field, with a default written as an assignment inside the literal; a
      // hole names none, and a rest, last, takes the positions after the
      // others. A field target's reference, its receiver and then its key, is
      // evaluated before its position is read and defaulted.
      const names = new Set<string>();
      const named = (target: Node): Expr => {
        if (ts.isIdentifier(target)) {
          if (target.text === "undefined")
            this.fail(target, "shadowing undefined is outside the fragment");
          if (names.has(target.text)) this.fail(target, "duplicate pattern binding");
          names.add(target.text);
          return { k: "id", pos: this.span(target), name: this.local(target) };
        }
        if (!ts.isPropertyAccessExpression(target) && !ts.isElementAccessExpression(target))
          this.fail(target, "an array assignment pattern writes a local or a field");
        const reference = this.expr(target);
        if (reference.k !== "read" && reference.k !== "index")
          this.fail(target, "an array assignment pattern writes a local or a field");
        return reference;
      };
      let rest: Extract<Expr, { k: "arrayAssign" }>["rest"] = null;
      const targets: ArrayElemAst[] = node.left.elements.flatMap((el, index): ArrayElemAst[] => {
        if (ts.isOmittedExpression(el)) return [];
        if (ts.isSpreadElement(el)) {
          rest = { index, pos: this.span(el), target: named(el.expression),
            slice: this.slices.has(this.span(node.right).join(":")) };
          return [];
        }
        const target =
          ts.isBinaryExpression(el) &&
          el.operatorToken.kind === ts.SyntaxKind.EqualsToken
            ? el.left
            : el;
        const dflt =
          ts.isBinaryExpression(el) &&
          el.operatorToken.kind === ts.SyntaxKind.EqualsToken
            ? el.right
            : null;
        return [{
          index,
          target: named(target),
          default_: dflt ? this.expr(dflt) : null,
        }];
      });
      if (targets.length === 0 && !rest) this.fail(node.left, "an empty pattern binds nothing");
      this.steppedPattern(ts.isArrayLiteralExpression(skipParentheses(node.right)), this.assignedSteps(node.left));
      return {
        k: "arrayAssign",
        pos: this.span(node),
        targets,
        rest,
        rhs: this.expr(node.right),
      };
    }
    if (node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      // Assigning a name is assigning a mutable local. Whether one was
      // declared is the adapter's to check: it builds the scope, and a name
      // that is not a mutable local there has no slot to write.
      if (ts.isIdentifier(node.left)) {
        if (node.left.text === "undefined")
          this.fail(node.left, "shadowing undefined is outside the fragment");
        return {
          k: "assign",
          pos: this.span(node),
          name: this.local(node.left),
          namePos: this.span(node.left),
          rhs: this.expr(node.right),
        };
      }
      // `o[k] = v` with `k` a `unique symbol` constant is the named write of
      // that symbol's key, as the read is.
      const symbolKey = ts.isElementAccessExpression(node.left)
        ? this.symbolKeys.get(this.span(node.left.argumentExpression).join(":")) : undefined;
      if (symbolKey !== undefined && ts.isElementAccessExpression(node.left) && !node.left.questionDotToken)
        return { k: "write", pos: this.span(node), field: { symbol: symbolKey },
          receiver: this.expr(node.left.expression), rhs: this.expr(node.right) };
      if (
        ts.isElementAccessExpression(node.left) &&
        !node.left.questionDotToken
      )
        return {
          k: "indexWrite",
          pos: this.span(node),
          receiver: this.expr(node.left.expression),
          key: this.expr(node.left.argumentExpression),
          rhs: this.expr(node.right),
        };
      if (
        !ts.isPropertyAccessExpression(node.left) ||
        node.left.questionDotToken
      )
        this.fail(node.left, "only field and local assignments are supported");
      return {
        k: "write",
        pos: this.span(node),
        field: ts.isPropertyAccessExpression(node.left)
          ? (this.staticPrivate(node.left) !== null
            ? this.fail(node.left, "a write to a static member: statics are immutable bindings")
            : this.memberKey(node.left.name))
          : this.fail(
              node.left,
              "only field and local assignments are supported",
            ),
        receiver: this.expr(
          ts.isPropertyAccessExpression(node.left)
            ? node.left.expression
            : this.fail(
                node.left,
                "only field and local assignments are supported",
              ),
        ),
        rhs: this.expr(node.right),
      };
    }
    const ops: Record<number, string> = {
      [ts.SyntaxKind.EqualsEqualsEqualsToken]: "===",
      [ts.SyntaxKind.ExclamationEqualsEqualsToken]: "!==",
      [ts.SyntaxKind.EqualsEqualsToken]: "==",
      [ts.SyntaxKind.ExclamationEqualsToken]: "!=",
      [ts.SyntaxKind.AmpersandAmpersandToken]: "&&",
      [ts.SyntaxKind.BarBarToken]: "||",
    };
    const op = ops[node.operatorToken.kind];
    if (!op)
      this.fail(
        node,
        `binary operator outside the fragment (${this.text(node.operatorToken)})`,
      );
    if (op === "===" || op === "!==" || op === "==" || op === "!=") {
      // Both operands of a typeof/literal test are strings, so loose equality
      // has the same result as strict equality and runs no conversion hook.
      const unwrap = (e: Expression): Expression =>
        ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e;
      const left = unwrap(node.left),
        right = unwrap(node.right);
      const shapes: readonly TypeofShape[] = ["number", "string", "boolean", "undefined", "function", "bigint", "symbol", "object"];
      const shapeOf = (e: Expression): TypeofShape | undefined =>
        ts.isStringLiteral(e) ? shapes.find((s) => s === e.text) : undefined;
      const pair =
        ts.isTypeOfExpression(left) && shapeOf(right)
          ? { operand: left, shape: shapeOf(right) }
          : ts.isTypeOfExpression(right) && shapeOf(left)
            ? { operand: right, shape: shapeOf(left) }
            : null;
      if (pair?.shape)
        return {
          k: "typeofTest",
          pos: this.span(node),
          shape: pair.shape,
          equal: op === "===" || op === "==",
          e: this.expr(pair.operand.expression),
        };
    }
    return {
      k: "bin",
      pos: this.span(node),
      op,
      l: this.expr(node.left),
      r: this.expr(node.right),
    };
  }

  /* ----------------------------------------------------------- closures -- */
  // A closure body is an expression in the calculus. A block-bodied one is
  // lowered here, once, so the verifier never has to guess how statements
  // inside a closure become one: the parser owns that translation because it
  // owns what the source means.

  private lambda(
    node: ArrowFunction | FunctionExpression | MethodDeclaration,
    instance?: TypeTerm,
    member?: PropertyKey,
  ): Expr {
    // A method's accessibility is TypeScript's alone (`CLASS_ACCESS`); a static
    // one is bound on its own (`classStmt`).
    const modifiers = (node.modifiers ?? []).filter((m) => !(ts.isMethodDeclaration(node) &&
      (CLASS_ACCESS.includes(m.kind) || m.kind === ts.SyntaxKind.StaticKeyword)));
    const isAsync = modifiers.length === 1 && modifiers[0]?.kind === ts.SyntaxKind.AsyncKeyword;
    if (modifiers.length && !isAsync)
      this.fail(node, "expected a closure without modifiers other than `async`");
    const ordinary = !ts.isArrowFunction(node);
    if (!ts.isArrowFunction(node)) {
      if (node.asteriskToken)
        this.fail(node, GENERATOR);
      // A named function expression binds its own name inside itself. A name
      // the function never refers to binds nothing it reads; one it does refer
      // to is a recursive binding, which the fragment has no frame for, as for
      // a cyclic closure initialization.
      if (ts.isFunctionExpression(node) && node.name) {
        const own = node.name.text;
        let uses = false;
        const visit = (n: Node): void => {
          if (uses) return;
          if (ts.isPropertyAccessExpression(n)) {
            visit(n.expression);
            return;
          }
          if (ts.isIdentifier(n) && n.text === own) uses = true;
          n.forEachChild(visit);
        };
        node.parameters.forEach(visit);
        if (node.body) visit(node.body);
        if (uses)
          this.fail(
            node,
            "a function expression that refers to its own name is a recursive binding, outside the fragment",
          );
      }
      if (ts.isMethodDeclaration(node) && node.postfixToken)
        this.fail(
          node,
          "an optional or definite method is outside the fragment",
        );
    }
    // An ordinary function's leading `this: T` states its receiver; without
    // one, any receiver is accepted. An arrow cannot declare one. A class
    // method's states a type its host, the instance it is read from, must
    // meet, which a generic method's scheme does not state.
    const head = node.parameters[0];
    const stated =
      !!head && ts.isIdentifier(head.name) && head.name.text === "this";
    if (stated && instance && node.typeParameters?.length)
      this.fail(head, GENERIC_METHOD_RECEIVER);
    if (stated && !ordinary)
      this.fail(head, "an arrow cannot declare a receiver");
    if (
      stated &&
      (!head.type ||
        head.questionToken ||
        head.dotDotDotToken ||
        head.initializer)
    )
      this.fail(head, "a receiver needs a required type annotation");
    const parameters = stated ? node.parameters.slice(1) : [...node.parameters];
    const body = node.body;
    if (!body) this.fail(node, "a function must have a body");
    // A directive prologue in the function's own body makes it strict. It
    // is a syntax error beside parameters that are not simple.
    const prologue = ts.isBlock(body)
      ? this.useStrict(body.statements)
      : { strict: false, skip: new Set<Statement>() };
    if (
      prologue.strict &&
      parameters.some((p) => p.initializer || p.dotDotDotToken)
    )
      this.fail(node, '"use strict" beside non-simple parameters');
    const outerStrict = this.strict;
    const outerReceiverMode = this.receiverMode;
    const outerAsync = this.asyncBody;
    this.strict = outerStrict || prologue.strict;
    if (ordinary) {
      this.receiverMode = this.strict ? "strict" : "sloppy";
    }
    // A class's generic method is the instance's member with quantified
    // signatures. Its closure's binders are named by the member's key and
    // the binder's position, so the producer's claims and the closure's
    // annotations name them alike; the closure's scheme binds them.
    const typeParams = this.enterTypeParams(node.typeParameters, member === undefined ? undefined :
      (tp, index) => {
        if (tp.constraint)
          this.fail(tp, "a bounded type parameter of a generic class method is outside the fragment: its binder row is named by its bound");
        return `${JSON.stringify(member)}#${index}`;
      });
    try {
      this.asyncBody = isAsync;
      const receiver = !ordinary
        ? null
        : {
            // A class method's receiver is its instance, or the type its
            // `this` parameter states.
            type: stated
              ? this.typeOf(head.type, head)
              : instance ? instance : ({ k: "atom", name: "unknown", span: this.span(node) } satisfies TypeTerm),
            strict: this.strict,
          };
      // Each name is taken where its parameter has just been checked: a
      // narrowing does not survive into the second pass over the same list.
      const bound = new Set<string>();
      const patterns: (PatternAst | null)[] = parameters.map((p) =>
        ts.isIdentifier(p.name) ? null : this.pattern(p.name, bound));
      for (const p of parameters) {
        if (ts.isIdentifier(p.name) && p.name.text === "this")
          this.fail(p, "expected an ordinary closure parameter");
        if (!ts.isIdentifier(p.name) && p.dotDotDotToken)
          this.fail(p, "a rest parameter pattern is outside the fragment");
        if (p.questionToken && p.initializer)
          this.fail(p, "a parameter cannot be both optional and defaulted");
        if (p.dotDotDotToken) {
          if (p.questionToken || p.initializer)
            this.fail(p, "a rest parameter is neither optional nor defaulted");
          if (p !== parameters[parameters.length - 1])
            this.fail(p, "a rest parameter must be the last one");
        }
        if (
          !p.questionToken &&
          !p.initializer &&
          !p.dotDotDotToken &&
          parameters.indexOf(p) > firstOptional(parameters)
        )
          this.fail(p, "a required parameter cannot follow an optional one");
        if (ts.isIdentifier(p.name) && p.name.text === "undefined")
          this.fail(p, "shadowing undefined is outside the fragment");
      }

      // A closure without a result annotation leaves its result to the
      // producer: the claim at the closure states it, and the body is checked
      // against that claim. A class method's result is its instance type's
      // member, which states it, so a method still needs the annotation.
      const declaredResult: TypeTerm | null =
        node.type || instance ? this.typeOf(node.type, node) : null;
      const arrow = ts.isArrowFunction(node) ? this.span(node.equalsGreaterThanToken) : null;
      const keyword = modifiers[0];
      const rest = (p: ts.ParameterDeclaration) => p.dotDotDotToken ? { rest: true as const } : {};
      // A parameter a pattern did not read is named by an identifier.
      const identifierOf = (p: ts.ParameterDeclaration): Identifier =>
        ts.isIdentifier(p.name) ? p.name : this.fail(p, "a parameter pattern makes the body a block");
      // A block body, or a parameter written as a pattern, makes the body
      // statements, lowered as a function's are: a parameter written as a
      // pattern or with a default binds a hidden name, which the caller's
      // argument initializes, and a `destructure` over it, first in the body
      // in parameter order, binds the source's names, the default replacing
      // an undefined argument, as JavaScript initializes parameters.
      if (ts.isBlock(body) || patterns.some((t) => t !== null)) {
        const bindings: Stmt[] = [];
        const params = parameters.map((p, i) => {
          if (ts.isIdentifier(p.name) && !p.initializer)
            return {
              name: this.local(p.name),
              type: p.dotDotDotToken ? this.restType(p) : this.closureParamType(p),
              ...rest(p),
            };
          const hidden = parameterName(i);
          const at = this.span(p.name);
          bindings.push({
            k: "destructure",
            pos: this.span(p),
            target: patterns[i] ?? { k: "name", name: this.local(identifierOf(p)), pos: at },
            default_: p.initializer ? this.expr(p.initializer) : null,
            init: { k: "id", pos: at, name: hidden },
          });
          // A caller may pass `undefined` where there is a default.
          return {
            name: hidden,
            type: !p.type ? (p.initializer ? optionalTerm(this.closureParamType(p), this.span(p)) : this.closureParamType(p))
              : p.questionToken || p.initializer ? this.optionalTypeOf(p.type, p) : this.typeOf(p.type, p),
          };
        });
        this.initializedBefore(node, params.map((q): [PatternAst, Expr | null] => {
          const b = bindings.find((st) => st.k === "destructure" && st.init.k === "id" && st.init.name === q.name);
          return b?.k === "destructure" ? [b.target, b.default_] : [{ k: "name", name: q.name, pos: this.span(node) }, null];
        }));
        let statements: Stmt[];
        if (ts.isBlock(body)) {
          const stmts = this.statements(body.statements.filter((s) => !prologue.skip.has(s)));
          // A body that can complete returns `undefined` at its closing
          // brace, the literal there too; an async one, `%AsyncComplete%()`.
          const brace: Span = [body.end - 1, body.end];
          statements = isAsync ? this.asyncCompletion(body, stmts)
            : completes(stmts) ? [...stmts, { k: "return", pos: brace,
                e: { k: "lit", pos: brace, lit: { a: "undefined" } } }]
            : stmts;
        } else {
          // An expression body is its return: `%AsyncReturn%(e)` when async,
          // the call at `=>`, the intrinsic read at `async`.
          const e = isAsync && arrow && keyword
            ? this.intrinsic(asyncReturnName, arrow, this.span(keyword), [this.expr(body)])
            : this.expr(body);
          statements = [{ k: "return", pos: this.span(body), e }];
        }
        return {
          k: "lambda",
          pos: this.span(node),
          typeParams,
          receiver,
          params,
          result: declaredResult,
          body: { k: "blockBody", pos: this.span(body), body: [...bindings, ...statements] },
        };
      }
      const inner = isAsync && arrow && keyword
        ? this.intrinsic(asyncReturnName, arrow, this.span(keyword), [this.expr(body)])
        : this.expr(body);
      const defaults = parameters.map((p) => p.initializer ? this.expr(p.initializer) : null);
      // A parameter default's own schedule is Lean's (`parameterOrder`).
      this.initializedBefore(node, parameters.map((p): [PatternAst, Expr | null] =>
        [{ k: "name", name: this.local(identifierOf(p)), pos: this.span(p.name) }, null]));
      return {
        k: "lambda",
        pos: this.span(node),
        typeParams,
        receiver,
        params: parameters.map((p, i) => ({
          name: this.local(identifierOf(p)),
          // A defaulted parameter's type is what the body reads; the default
          // itself is the expression that replaces an omitted argument. A rest
          // parameter's type is the tuple its arguments are collected into.
          type: p.dotDotDotToken ? this.restType(p) : this.closureParamType(p),
          ...(defaults[i] ? { default: defaults[i] } : {}),
          ...rest(p),
        })),
        result: declaredResult,
        body: inner,
      };
    } finally {
      this.leaveTypeParams();
      this.strict = outerStrict;
      this.receiverMode = outerReceiverMode;
      this.asyncBody = outerAsync;
    }
  }

  /* -------------------------------------------------------- statements -- */

  /* `const pattern = init;`. One declarator; object and array patterns,
     nested, with identifier keys, defaults, holes and an array rest: what the
     lowering states. */
  private patternStmt(list: ts.VariableDeclarationList, node: Node, mutable: boolean): Stmt {
    if (mutable)
      this.fail(node, "a `let` pattern whose bindings are assigned in a `for` head is outside the fragment: its bindings are cells, which only a statement of a block lowers them to (one never assigned is a `const` pattern)");
    if (list.declarations.length !== 1)
      this.fail(node, "a pattern declares alone in the fragment");
    const d = list.declarations[0];
    if (d.type) this.fail(d, "an annotated pattern is outside the fragment");
    if (!d.initializer) this.fail(d, "a `const` needs an initializer");
    const kind = this.iterations.get(this.span(d.initializer).join(":"));
    if (ts.isArrayBindingPattern(d.name) && kind?.startsWith("client")) {
      if (kind === "client-unclosable" && !d.name.elements.some((e) => ts.isBindingElement(e) && e.dotDotDotToken))
        this.fail(d.initializer, UNCLOSABLE);
      return this.protocolPattern(d.name, d.initializer, node, kind === "client-method");
    }
    const target = this.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
    this.initializedBefore(d, [[target, null]]);
    return {
      k: "destructure",
      pos: this.span(node),
      target,
      default_: null,
      init: this.expr(d.initializer),
    };
  }

  /** `const [a, , b, ...r] = e` over a program's iterable, as ECMA-262's
   * IteratorBindingInitialization runs it: GetIterator, one IteratorStepValue
   * per element until one is done, a hole stepping too; the rest collects
   * every value left; then, the iterator not done (no rest took it to its
   * end), IteratorClose. In ordinary forms, the steps before the source's
   * own declaration, which binds the names from cells no source spells:
   *
   *     let %v0 = undefined, %v2 = undefined;
   *     const %rest = [], %iterator = e[Symbol.iterator](), %next = …;
   *     %done: {
   *       const %result0 = %next(); if (%result0.done) break %done; %v0 = %result0.value;
   *       …
   *       while (true) { const %resultR = %next(); if (%resultR.done) break %done; %rest.push(%resultR.value); }
   *       // or, without a rest, the close of `protocolForOf`
   *     }
   *     const a = %v0, b = %v2, r = %rest;
   *
   * Binding a name runs nothing, so binding each after the steps is binding
   * it at its step. A default or a nested pattern, which run code between
   * the steps (and IteratorClose on a throw of theirs), is outside it. */
  private protocolPattern(pattern: ts.ArrayBindingPattern, init: Expression, node: Node, method: boolean): Stmt {
    if (this.hoist?.stmt !== node)
      this.fail(node, "an array pattern over a program's iterable is outside the fragment here: its steps are statements, with cells, before the declaration, which a function's or a closure's body has and a module's top level or a `for` initializer does not");
    const site = this.hoist.site;
    const tag = `${pattern.getStart(this.file)}`;
    const label = `%done@${tag}`;
    const elements = pattern.elements;
    const rest = elements.at(-1);
    const restName = rest && ts.isBindingElement(rest) && rest.dotDotDotToken ? rest : null;
    const named: { cell: string; name: ts.Identifier }[] = [];
    elements.forEach((el, i) => {
      if (!ts.isBindingElement(el) || !el.name || el === restName) return;
      if (el.initializer || !el.name || !ts.isIdentifier(el.name) || el.dotDotDotToken)
        this.fail(el, "a default or a nested pattern in an array pattern over a program's iterable is outside the fragment: it runs code between the iterator's steps, which the lowering does not interleave");
      if (el.name.text === "undefined") this.fail(el, "shadowing undefined is outside the fragment");
      named.push({ cell: `%v${i}@${tag}`, name: el.name });
    });
    if (restName && (!restName.name || !ts.isIdentifier(restName.name)))
      this.fail(restName, "a nested pattern in an array pattern's rest over a program's iterable is outside the fragment");
    const restCell = `%rest@${tag}`;
    const statements: Stmt[] = [];
    if (named.length) {
      const e = site.entry();
      statements.push({ k: "let", pos: [e, e + 1], bindings: named.map(({ cell }) => {
        const at = site.span();
        return { name: cell, namePos: at, annot: null, init: { k: "lit", pos: at, lit: { a: "undefined" } } };
      }) });
    }
    const start = this.protocolStart(this.expr(init), site, tag, init);
    const e0 = site.entry();
    const restAt = site.span();
    const restBinding: BindingAst[] = restName
      ? [{ name: restCell, namePos: restAt, annot: null, init: { k: "arrayLit", pos: restAt, elems: [] } }] : [];
    statements.push({ k: "const", pos: [e0, e0 + 1], bindings: [...restBinding, ...start.bindings] });
    const leave = (): Stmt => {
      const e = site.entry();
      return { k: "break", pos: [e, e + 1], label };
    };
    const inner: Stmt[] = [];
    elements.forEach((el, i) => {
      if (el === restName) return;
      const step = this.protocolStep(start.next, `%result${i}@${tag}`, leave, site);
      inner.push(...step.stmts);
      const cell = named.find((n) => n.cell === `%v${i}@${tag}`);
      if (cell) {
        const e = site.entry();
        const at = site.span();
        inner.push({ k: "effect", pos: [e, e + 1],
          e: { k: "assign", pos: at, name: cell.cell, namePos: site.span(), rhs: step.value() } });
      }
    });
    if (restName) {
      const eLoop = site.entry();
      inner.push({ k: "while", pos: [eLoop, eLoop + 1], update: [],
        cond: { k: "lit", pos: site.span(), lit: { a: "booleanlit", v: "true" } },
        body: this.collectStep(start.next, `%resultRest@${tag}`, restCell, leave, site) });
    } else inner.push(...this.closeStatements(start.iteratorAt, tag, site, method));
    statements.push({ k: "block", pos: this.span(node), label, body: inner });
    this.hoisted.push(...statements);
    const bindings: BindingAst[] = named.map(({ cell, name }) => ({ name: this.local(name),
      namePos: this.span(name), annot: null, init: { k: "id", pos: this.span(name), name: cell } }));
    if (restName && restName.name && ts.isIdentifier(restName.name))
      bindings.push({ name: this.local(restName.name), namePos: this.span(restName.name), annot: null,
        init: { k: "id", pos: this.span(restName.name), name: restCell } });
    return { k: "const", pos: this.span(node), bindings };
  }

  /** One step of a collecting loop: the step, its `done` leaving by `leave`,
   * and the value pushed onto the fresh array `items`. */
  private collectStep(next: string, result: string, items: string, leave: () => Stmt,
      site: { entry(): number; span(): Span }): Stmt[] {
    const step = this.protocolStep(next, result, leave, site);
    const e = site.entry();
    const pushAt = site.span(), pushRead = site.span(), itemsAt = site.span();
    return [...step.stmts, { k: "effect", pos: [e, e + 1], e: { k: "invoke", pos: pushAt, args: [step.value()],
      callee: { k: "read", pos: pushRead, field: "push", e: { k: "id", pos: itemsAt, name: items } } } }];
  }

  /** IteratorClose where nothing is thrown: the iterator's `return`, read
   * once, called on it where it is not `undefined`, its result an object
   * (`protocolForOf`). A `return` the iterator's type declares a required
   * method (`method`) is a method member, read bound to the iterator
   * (`o.m.bind(o)`, which reads it once) and always present. */
  private closeStatements(iteratorAt: () => Expr, tag: string, site: { entry(): number; span(): Span },
      method: boolean): Stmt[] {
    const member = `%return@${tag}`, closed = `%closed@${tag}`;
    const e1 = site.entry();
    if (method) {
      const e2 = site.entry();
      const boundAt = site.span(), readAt = site.span(), callAt = site.span(), memberAt = site.span(),
        objectAt = site.span();
      return [
        { k: "const", pos: [e1, e1 + 1], bindings: [{ name: member, namePos: boundAt, annot: null,
          init: { k: "bindWithReceiver", pos: boundAt, args: [],
            callee: { k: "read", pos: readAt, field: "return", e: iteratorAt() }, receiver: iteratorAt() } }] },
        { k: "const", pos: [e2, e2 + 1], bindings: [{ name: closed, namePos: callAt,
          annot: { k: "atom", name: "object", span: objectAt },
          init: { k: "apply", pos: callAt, callee: { k: "id", pos: memberAt, name: member }, args: [] } }] },
      ];
    }
    const e2 = site.entry(), e3 = site.entry();
    const readAt = site.span(), testAt = site.span(), narrowed = site.span(), callAt = site.span(),
      objectAt = site.span();
    return [
      { k: "const", pos: [e1, e1 + 1], bindings: [{ name: member, namePos: readAt, annot: null,
        init: { k: "read", pos: readAt, field: "return", e: iteratorAt() } }] },
      { k: "if", pos: [e2, e2 + 1],
        // The member's read and the name holding it are one value, at one
        // claim site.
        cond: { k: "typeofTest", pos: testAt, shape: "undefined", equal: false,
          e: { k: "id", pos: readAt, name: member } },
        then: [{ k: "const", pos: [e3, e3 + 1], bindings: [{ name: closed, namePos: callAt,
          annot: { k: "atom", name: "object", span: objectAt },
          init: { k: "callWithReceiver", pos: callAt, callee: { k: "id", pos: narrowed, name: member },
            receiver: iteratorAt(), args: [] } }] }],
        else_: null },
    ];
  }

  /** A spread of a program's iterable, `...e`, collected into a fresh array
   * before the statement it is in (`hoist`): the steps of `protocolForOf`,
   * closing nothing (a spread steps until done), each value pushed onto the
   * array, which the spread then stands for. */
  private collect(operand: Expression): Expr {
    const hoist = this.hoist;
    if (!hoist) throw Error("internal: a spread collected outside its statement");
    const site = hoist.site;
    const tag = `${operand.getStart(this.file)}`;
    const items = `%items@${tag}`;
    const start = this.protocolStart(this.expr(operand), site, tag, operand);
    const e0 = site.entry();
    const itemsAt = site.span();
    const eLoop = site.entry();
    const leave = (): Stmt => {
      const e = site.entry();
      return { k: "break", pos: [e, e + 1], label: null };
    };
    this.hoisted.push(
      { k: "const", pos: [e0, e0 + 1], bindings: [
        { name: items, namePos: itemsAt, annot: null, init: { k: "arrayLit", pos: itemsAt, elems: [] } },
        ...start.bindings] },
      { k: "while", pos: [eLoop, eLoop + 1], update: [],
        cond: { k: "lit", pos: site.span(), lit: { a: "booleanlit", v: "true" } },
        body: this.collectStep(start.next, `%result@${tag}`, items, leave, site) });
    return { k: "id", pos: site.span(), name: items };
  }

  /** The spread of a program's iterable the statement `s` runs, where the
   * collection may run before the statement: the one element of an array
   * literal, or an argument of a call of a name, every operand before it a
   * name or a literal, none of them assigned anywhere in the file, so that
   * what they hold before the iterator's code runs is what they hold after.
   * The literal or call is the statement's value: an expression statement's,
   * a `return`'s or a declaration's one initializer. */
  private hoistTarget(s: Statement): ts.SpreadElement | null {
    let e: Expression | undefined;
    if (ts.isExpressionStatement(s)) e = s.expression;
    else if (ts.isReturnStatement(s)) e = s.expression;
    else if (ts.isVariableStatement(s)) {
      const [only, ...others] = s.declarationList.declarations;
      if (only && !others.length && ts.isIdentifier(only.name)) e = only.initializer;
    }
    if (!e) return null;
    const program = (x: Node) => {
      const kind = this.iterations.get(this.span(x).join(":"));
      return !!kind?.startsWith("client");
    };
    if (ts.isArrayLiteralExpression(e)) {
      const [only, ...others] = e.elements;
      return only && !others.length && ts.isSpreadElement(only) && program(only.expression) ? only : null;
    }
    if (!ts.isCallExpression(e) || e.questionDotToken || !ts.isIdentifier(e.expression)) return null;
    const index = e.arguments.findIndex((a) => ts.isSpreadElement(a) && program(a.expression));
    const spread = e.arguments[index];
    if (!spread || !ts.isSpreadElement(spread)) return null;
    const assigned = this.assignedNames();
    const stable = (x: Node) => ts.isIdentifier(x) ? !assigned.has(x.text)
      : ts.isNumericLiteral(x) || ts.isStringLiteral(x) || x.kind === ts.SyntaxKind.TrueKeyword ||
        x.kind === ts.SyntaxKind.FalseKeyword || x.kind === ts.SyntaxKind.NullKeyword;
    return stable(e.expression) && e.arguments.slice(0, index).every(stable) ? spread : null;
  }

  /** The names the file assigns anywhere: an assignment, a compound or
   * logical one, an update, a destructuring assignment. */
  private assignedNames(): Set<string> {
    if (this.assigned) return this.assigned;
    const names = new Set<string>();
    const targets = (e: Node): void => {
      while (ts.isParenthesizedExpression(e)) e = e.expression;
      if (ts.isIdentifier(e)) names.add(e.text);
      else if (ts.isArrayLiteralExpression(e)) e.elements.forEach(targets);
      else if (ts.isObjectLiteralExpression(e)) e.properties.forEach((p) =>
        ts.isShorthandPropertyAssignment(p) ? (ts.isIdentifier(p.name) ? names.add(p.name.text) : undefined)
          : ts.isPropertyAssignment(p) ? targets(p.initializer)
          : ts.isSpreadAssignment(p) ? targets(p.expression) : undefined);
      else if (ts.isSpreadElement(e)) targets(e.expression);
      else if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) targets(e.left);
    };
    const visit = (n: Node): void => {
      if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
          n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) targets(n.left);
      if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
          (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
        targets(n.operand);
      if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer))
        targets(n.initializer);
      n.forEachChild(visit);
    };
    visit(this.file);
    this.assigned = names;
    return names;
  }

  /* Each default of a declaration's patterns, in binding order, reads none
     of the declaration's own names not yet initialized: JavaScript throws
     there (the temporal dead zone), where the lowering would read whatever
     outer binding has the name. */
  private initializedBefore(at: Node, targets: [PatternAst, Expr | null][]): void {
    const own = new Set(targets.flatMap(([t]) => patternNames(t)));
    const bound = new Set<string>();
    const check = (d: Expr | null): void => {
      if (d && [...namesRead(d)].some((n) => own.has(n) && !bound.has(n)))
        this.fail(at, "a default reads a binding of its own declaration before it is initialized");
    };
    const visit = (t: PatternAst, d: Expr | null): void => {
      check(d);
      if (t.k === "name") bound.add(t.name);
      else if (t.k === "object") {
        for (const q of t.props) visit(q.target, q.default_);
        if (t.rest) visit(t.rest.target, null);
      }
      else {
        for (const q of t.elems) visit(q.target, q.default_);
        if (t.rest) visit(t.rest.target, null);
      }
    };
    for (const [t, d] of targets) visit(t, d);
  }

  /* Whether evaluating `e` runs no code but its own and writes nothing but a
     local: a literal, a name, a field read (the heap has data properties
     only), a read at a literal key, `!`, `typeof`, `void`, a sign of a
     literal, `===`, `!==`, `&&`, `||`, `??`, a comma, a conditional, an
     assignment of a local, an array or object literal of such parts, a
     closure's creation. Anything else may call, convert an object or write a
     field. */
  private inert(e: Node): boolean {
    if (ts.isNumericLiteral(e) || ts.isBigIntLiteral(e) || ts.isStringLiteral(e) ||
        ts.isNoSubstitutionTemplateLiteral(e) || ts.isIdentifier(e) || ts.isArrowFunction(e) ||
        ts.isFunctionExpression(e) || ts.isOmittedExpression(e))
      return true;
    switch (e.kind) {
      case ts.SyntaxKind.TrueKeyword: case ts.SyntaxKind.FalseKeyword:
      case ts.SyntaxKind.NullKeyword: case ts.SyntaxKind.ThisKeyword:
        return true;
    }
    if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) ||
        ts.isNonNullExpression(e) || ts.isPropertyAccessExpression(e) || ts.isTypeOfExpression(e) ||
        ts.isVoidExpression(e))
      return this.inert(e.expression);
    if (ts.isElementAccessExpression(e))
      return this.inert(e.expression) && (ts.isStringLiteral(e.argumentExpression) ||
        ts.isNumericLiteral(e.argumentExpression));
    if (ts.isPrefixUnaryExpression(e))
      return e.operator === ts.SyntaxKind.ExclamationToken ? this.inert(e.operand)
        : (e.operator === ts.SyntaxKind.MinusToken || e.operator === ts.SyntaxKind.PlusToken) &&
          (ts.isNumericLiteral(e.operand) || ts.isBigIntLiteral(e.operand));
    if (ts.isConditionalExpression(e))
      return this.inert(e.condition) && this.inert(e.whenTrue) && this.inert(e.whenFalse);
    if (ts.isBinaryExpression(e)) {
      const op = e.operatorToken.kind;
      if (op === ts.SyntaxKind.EqualsToken) return ts.isIdentifier(e.left) && this.inert(e.right);
      return (op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken ||
        op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken ||
        op === ts.SyntaxKind.QuestionQuestionToken || op === ts.SyntaxKind.CommaToken) &&
        this.inert(e.left) && this.inert(e.right);
    }
    if (ts.isArrayLiteralExpression(e)) return e.elements.every((x) => !ts.isSpreadElement(x) && this.inert(x));
    if (ts.isObjectLiteralExpression(e))
      return e.properties.every((p) => ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer ||
        ts.isPropertyAssignment(p) && !ts.isComputedPropertyName(p.name) && this.inert(p.initializer));
    return false;
  }

  /* The defaults a binding pattern runs, at any depth. */
  private patternDefaults(node: ts.BindingName): Node[] {
    if (ts.isIdentifier(node)) return [];
    return node.elements.flatMap((el): Node[] => ts.isOmittedExpression(el) ? []
      : [...(el.initializer ? [el.initializer] : []), ...(el.name ? this.patternDefaults(el.name) : [])]);
  }

  /* JavaScript steps an array pattern's source through the array's iterator,
     which stays finished once a step found the end; the lowering reads each
     position when its step runs (`positionRead`, a rest's collection), which
     is that step while nothing has grown the array since a step found the
     end. Code that may change an array, run after one step and before a later
     one, could do so: `[, box[(xs.push(1, 2), "slot")] = 9] = xs` with `xs`
     empty writes 9 where a read of position 1 finds 2. Over a fresh array
     literal no other reference reaches the array; over any other source such
     code is refused. Each element is its target's reference, evaluated before
     its step (`before`, a field target's receiver and key), and what runs
     after its step (`after`: its default, a nested pattern's defaults, and a
     write at a field target's index or `length`, which may be the array's).
     A write at another named field changes no array's elements or length. */
  private steppedPattern(fresh: boolean,
      elements: { node: Node; hole: boolean; before: Node[]; after: Node[] }[]): void {
    if (fresh) return;
    let last = -1;
    elements.forEach((el, i) => { if (!el.hole) last = i; });
    const refuse = (node: Node, what: string): never => this.fail(node,
      `an array pattern over an array another reference may hold, with ${what} after one of its steps and before a later one, is outside the fragment: JavaScript steps the array's iterator, which stays finished once a step found the end, while the lowering reads each position, which sees what such code added to the array`);
    elements.forEach((el, i) => {
      if (i > 0 && i <= last)
        for (const n of el.before) if (!this.inert(n)) refuse(n, "a target's reference that may call or write");
      if (i < last)
        for (const n of el.after)
          if (ts.isPropertyAccessExpression(n) || ts.isElementAccessExpression(n)) refuse(n, "a write at a field target's index or length");
          else if (!this.inert(n)) refuse(n, "a default that may call or write");
    });
  }

  /* An array assignment's elements, as `steppedPattern` reads them. */
  private assignedSteps(left: ts.ArrayLiteralExpression):
      { node: Node; hole: boolean; before: Node[]; after: Node[] }[] {
    return left.elements.map((el) => {
      if (ts.isOmittedExpression(el)) return { node: el, hole: true, before: [], after: [] };
      const assigned = ts.isBinaryExpression(el) && el.operatorToken.kind === ts.SyntaxKind.EqualsToken;
      const target = ts.isSpreadElement(el) ? el.expression : assigned ? el.left : el;
      const before = ts.isPropertyAccessExpression(target) ? [target.expression]
        : ts.isElementAccessExpression(target) ? [target.expression, target.argumentExpression] : [];
      const write = ts.isElementAccessExpression(target) ||
        ts.isPropertyAccessExpression(target) && ts.isIdentifier(target.name) && target.name.text === "length"
        ? [target] : [];
      return { node: el, hole: false, before, after: [...(assigned ? [el.right] : []), ...write] };
    });
  }

  /* What a binding name or pattern binds. An object pattern reads identifier
     keys; its rest binds a fresh object holding the source's other own
     enumerable properties. An array pattern's hole is a position no element
     names; `fresh` says its source is an array literal (`steppedPattern`). */
  private pattern(node: ts.BindingName, names: Set<string>, fresh = false): PatternAst {
    if (ts.isIdentifier(node)) {
      if (node.text === "undefined")
        this.fail(node, "shadowing undefined is outside the fragment");
      if (names.has(node.text)) this.fail(node, "duplicate pattern binding");
      names.add(node.text);
      return { k: "name", name: this.local(node), pos: this.span(node) };
    }
    if (node.elements.length === 0)
      this.fail(node, "an empty pattern binds nothing");
    if (ts.isArrayBindingPattern(node)) {
      this.steppedPattern(fresh, node.elements.map((el) => ts.isOmittedExpression(el) || !el.name
        ? { node: el, hole: true, before: [], after: [] }
        : { node: el, hole: false, before: [],
            after: [...(el.initializer ? [el.initializer] : []), ...this.patternDefaults(el.name)] }));
      const elems: PatternElemAst[] = [];
      let rest: Extract<PatternAst, { k: "array" }>["rest"] = null;
      node.elements.forEach((el, index) => {
        // A hole is an omitted expression, or a binding element without a name.
        if (ts.isOmittedExpression(el) || !el.name) return;
        if (el.dotDotDotToken)
          rest = { index, pos: this.span(el), target: this.pattern(el.name, names),
            slice: this.slices.has(this.span(node).join(":")) };
        else
          elems.push({
            index,
            target: this.pattern(el.name, names),
            default_: el.initializer ? this.expr(el.initializer) : null,
          });
      });
      return { k: "array", pos: this.span(node), elems, rest };
    }
    // An object rest, last, copies the source's other own enumerable
    // properties onto a fresh object (DESIGN.md, "Object literals").
    let rest: Extract<PatternAst, { k: "object" }>["rest"] = null;
    const last = node.elements[node.elements.length - 1];
    if (last?.dotDotDotToken) {
      const restName = last.name;
      if (!restName || !ts.isIdentifier(restName)) return this.fail(last, "an object rest binds a name");
      rest = { pos: this.span(last), target: this.pattern(restName, names) };
    }
    const props: PatternPropAst[] = node.elements.filter((el) => !el.dotDotDotToken).map((el) => {
      if (!el.name) this.fail(el, "a pattern element needs a name");
      const key = el.propertyName ?? el.name;
      if (!ts.isIdentifier(key))
        this.fail(el, "computed or string pattern keys are outside the fragment");
      return {
        field: key.text,
        target: this.pattern(el.name, names),
        default_: el.initializer ? this.expr(el.initializer) : null,
      };
    });
    return { k: "object", pos: this.span(node), props, rest };
  }

  /* A branch or loop body. TypeScript allows a single statement where a block
     could be written, and the two mean the same thing here: a lexical
     declaration cannot be an unbraced body, so no binding's scope depends on
     the braces. */
  block(node: Statement): Stmt[] {
    if (!ts.isBlock(node)) {
      if (ts.isVariableStatement(node))
        this.fail(node, "a declaration requires a block body");
      return this.statements([node]);
    }
    return this.statements(node.statements);
  }

  /** A statement list, without its dead tail: the statements after one that
   * always completes abruptly (`abrupt`) are never reached, since nothing can
   * jump into the middle of a list. They are dropped unread when dropping them
   * changes no binding the live statements see: a `var` or function
   * declaration there is hoisted, and a `let`, `const` or `class` there binds
   * its name in the whole block, so a live reference to it would be to that
   * binding, forever uninitialized. */
  statements(list: readonly Statement[]): Stmt[] {
    const end = list.findIndex((s) => this.abrupt(s));
    const live = end < 0 ? list : list.slice(0, end + 1);
    const lexical = new Set<string>();
    const hoisted = (n: Node): Node | undefined => {
      if (ts.isFunctionDeclaration(n) ||
          (ts.isVariableDeclarationList(n) && !(n.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))))
        return n;
      if (ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n)) return undefined;
      return n.forEachChild(hoisted);
    };
    const names = (n: Node): void => {
      if (ts.isIdentifier(n)) lexical.add(n.text);
      else n.forEachChild(names);
    };
    for (const s of list.slice(live.length)) {
      const at = hoisted(s);
      if (at) this.fail(at, "a hoisted declaration after a statement that always jumps is outside the fragment");
      if (ts.isVariableStatement(s))
        for (const d of s.declarationList.declarations) names(d.name);
      else if (ts.isClassDeclaration(s) && s.name) lexical.add(s.name.text);
      else if (ts.SyntaxKind[s.kind].endsWith("Declaration"))
        this.fail(s, "a declaration after a statement that always jumps is outside the fragment");
    }
    const refers = (n: Node): Node | undefined =>
      ts.isIdentifier(n) && lexical.has(n.text) ? n : n.forEachChild(refers);
    for (const s of live) {
      const at = lexical.size ? refers(s) : undefined;
      if (at) this.fail(at, "a name declared only in dead code is outside the fragment");
    }
    // An empty statement, `;`, does nothing.
    return live.filter((s) => !ts.isEmptyStatement(s)).flatMap((s) => this.hoisting(s));
  }

  /** A statement, preceded by the statements its lowering runs before it:
   * the collection of a spread of a program's iterable (`collect`), or the
   * steps of an array pattern over one (`protocolPattern`). */
  private hoisting(s: Statement): Stmt[] {
    const savedHoist = this.hoist, savedHoisted = this.hoisted;
    let site: { entry(): number; span(): Span } | null = null;
    const lazy = () => site ??= this.sites(s);
    this.hoist = { stmt: s, spread: this.hoistTarget(s),
      site: { entry: () => lazy().entry(), span: () => lazy().span() } };
    this.hoisted = [];
    try {
      const stmts = (ts.isVariableStatement(s) ? this.letPattern(s) : null) ?? [this.stmt(s)];
      return [...this.hoisted, ...stmts];
    } finally {
      this.hoist = savedHoist;
      this.hoisted = savedHoisted;
    }
  }

  /** `let pattern = init;` whose bindings are written: the pattern binds
   * names no source spells, as a `const` pattern binds, then a `let` binds
   * each of the source's names to its value, a cell of its own whose
   * contract is as an unannotated `let`'s, its initializer's type widened.
   * JavaScript reads and defaults the pattern's positions, then initializes
   * the bindings, in the same order either way. Each cell is claimed at its
   * name, as the value it starts with is. Null for any other statement. */
  private letPattern(s: ts.VariableStatement): Stmt[] | null {
    const list = s.declarationList;
    const [d] = list.declarations;
    if (list.flags & ts.NodeFlags.Const || !(list.flags & ts.NodeFlags.Let) || list.declarations.length !== 1 ||
        !d || !(ts.isObjectBindingPattern(d.name) || ts.isArrayBindingPattern(d.name)) || this.neverAssigned(list))
      return null;
    if (d.type) this.fail(d, "an annotated pattern is outside the fragment");
    if (!d.initializer) this.fail(d, "a `let` pattern needs an initializer");
    // Over a program's iterable, an array pattern is the iterator's steps
    // (`protocolPattern`), which bind no cells.
    if (ts.isArrayBindingPattern(d.name) &&
        this.iterations.get(this.span(d.initializer).join(":"))?.startsWith("client"))
      return null;
    const target = this.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
    this.initializedBefore(d, [[target, null]]);
    const cells: BindingAst[] = [];
    const hide = (t: PatternAst): PatternAst => {
      switch (t.k) {
        case "name": {
          const hidden = `%let-pattern ${t.name}`;
          cells.push({ name: t.name, namePos: t.pos, annot: null, init: { k: "id", pos: t.pos, name: hidden } });
          return { ...t, name: hidden };
        }
        case "object": return { ...t, props: t.props.map((q) => ({ ...q, target: hide(q.target) })),
          rest: t.rest ? { ...t.rest, target: hide(t.rest.target) } : null };
        case "array": return { ...t, elems: t.elems.map((q) => ({ ...q, target: hide(q.target) })),
          rest: t.rest ? { ...t.rest, target: hide(t.rest.target) } : null };
      }
    };
    const hidden = hide(target);
    return [
      { k: "destructure", pos: this.span(s), target: hidden, default_: null, init: this.expr(d.initializer) },
      { k: "let", pos: this.span(d.name), bindings: cells },
    ];
  }

  /** The offset of `token` at or after `from`, past whitespace and comments:
   * a punctuator or keyword of `at` the tree has no node for. */
  private token(from: number, token: string, at: Node): number {
    const text = this.file.text;
    let i = from;
    for (;;) {
      if (/\s/.test(text[i] ?? "")) i++;
      else if (text.startsWith("//", i)) {
        const n = text.indexOf("\n", i);
        i = n < 0 ? text.length : n;
      } else if (text.startsWith("/*", i)) {
        const n = text.indexOf("*/", i + 2);
        i = n < 0 ? text.length : n + 2;
      } else break;
    }
    if (!text.startsWith(token, i)) this.fail(at, `expected \`${token}\``);
    return i;
  }

  /** `for (init; cond; update) body`: `init`, then the loop whose head tests
   * `cond` (`true` where it is absent, at the second `;`) and whose body's
   * end and every `continue` run `update`; with an `init`, in a block of its
   * own, the loop's entry at the first `;` (a block has none, and the `init`
   * statement's is at its start). A `let` declared there is one
   * binding for the whole loop, where
   * JavaScript copies it into each iteration: the two differ only for a
   * closure capturing it, which is refused. */
  private forStmt(node: ts.ForStatement): Stmt {
    const open = this.token(node.getStart(this.file) + "for".length, "(", node);
    const init = node.initializer;
    const first = this.token(init ? init.end : open + 1, ";", node);
    const second = this.token(node.condition ? node.condition.end : first + 1, ";", node);
    let initial: Stmt | null = null;
    if (init && ts.isVariableDeclarationList(init)) {
      if (init.flags & ts.NodeFlags.Let) {
        const names = new Set<string>();
        const collect = (n: Node): void => {
          if (ts.isIdentifier(n)) names.add(n.text);
          else n.forEachChild(collect);
        };
        for (const d of init.declarations) collect(d.name);
        const refers = (n: Node): Node | undefined =>
          ts.isIdentifier(n) && names.has(n.text) ? n : n.forEachChild(refers);
        const captures = (n: Node): Node | undefined =>
          ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n) ? refers(n) : n.forEachChild(captures);
        for (const part of [node.condition, node.incrementor, node.statement]) {
          const at = part && captures(part);
          if (at) this.fail(at, "a closure capturing a `for` loop's `let` binding is outside the fragment");
        }
      }
      initial = this.declarations(init, init);
    } else if (init && ts.isExpression(init)) initial = { k: "effect", pos: this.span(init), e: this.expr(init) };
    else if (init) this.fail(init, "a `for` initializer is a declaration or an expression");
    const loop: Stmt = {
      k: "while",
      pos: init ? [first, node.end] : this.span(node),
      cond: node.condition
        ? this.expr(node.condition)
        : { k: "lit", pos: [second, second + 1], lit: { a: "booleanlit", v: "true" } },
      body: this.block(node.statement),
      update: node.incrementor
        ? [{ k: "effect", pos: this.span(node.incrementor), e: this.expr(node.incrementor) }]
        : [],
    };
    return initial ? { k: "block", pos: this.span(node), label: null, body: [initial, loop] } : loop;
  }

  /** `for (const k in o) body` is `for (const k of %ForIn%(o)) body`: the
   * keys the loop visits, a string each (`intrinsics.mts`), the call at the
   * declaration, the intrinsic read at `in`. */
  private forInStmt(node: ts.ForInStatement): Stmt {
    const list = node.initializer;
    if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1 ||
        !(list.flags & ts.NodeFlags.Const || (list.flags & ts.NodeFlags.Let && this.neverAssigned(list, true))))
      this.fail(node, "a `for...in` loop declares one `const` binding, or a `let` nothing assigns");
    const d = list.declarations[0];
    if (!ts.isIdentifier(d.name)) this.fail(d, "destructuring is outside the fragment");
    if (d.type || d.initializer) this.fail(d, "a `for...in` binding takes the key's type");
    if (d.name.text === "undefined") this.fail(d, "shadowing undefined is outside the fragment");
    const keyword = this.token(list.end, "in", node);
    // A body reading the entry at the key before anything can change it
    // steps the entries: the key is the step's first element, each such read
    // its second.
    const reads = forInEntryReads(node);
    if (reads.length) {
      const entry = `%for-in@${node.getStart(this.file)}%`;
      for (const read of reads) this.entryReads.set(this.span(read).join(":"), entry);
      // The entry is bound at the head's declaration, the key at its name
      // from the entry's first element, read at `in`.
      const [start] = this.span(list);
      return {
        k: "forOf",
        pos: this.span(node),
        name: entry,
        namePos: this.span(list),
        iterate: iterateForInName,
        iterable: this.expr(node.expression),
        body: [
          { k: "const", pos: [start, start + 1], bindings: [{ name: this.local(d.name), namePos: this.span(d.name),
            annot: null, init: { k: "index", pos: [keyword, keyword + "in".length],
              e: { k: "id", pos: [keyword, keyword + 1], name: entry },
              key: { k: "lit", pos: [keyword + 1, keyword + 2], lit: { a: "numberlit", v: "0" } } } }] },
          ...this.block(node.statement),
        ],
      };
    }
    return {
      k: "forOf",
      pos: this.span(node),
      name: this.local(d.name),
      namePos: this.span(d.name),
      iterate: iterateName,
      iterable: this.intrinsic(forInName, this.span(list), [keyword, keyword + "in".length],
        [this.expr(node.expression)]),
      body: this.block(node.statement),
    };
  }

  /** `for (const x of e) S` over an iterable the program defines, an object
   * with its own `[Symbol.iterator]`, as ECMA-262's ForIn/OfBodyEvaluation
   * runs it: GetIterator, then IteratorStepValue until done, the body per
   * value, and IteratorClose where the body is left otherwise than by
   * completing or by a `continue` of the loop. In ordinary forms, under
   * names no source spells:
   *
   *     const %iterator = e[Symbol.iterator](), %next = %iterator.next.bind(%iterator);
   *     while (true) {
   *       const %result = %next();
   *       if (%result.done) break;
   *       const x = %result.value;
   *       closing { S } close {
   *         const %return = %iterator.return;
   *         if (typeof %return !== "undefined") { const %closed: object = %return.call(%iterator); }
   *       }
   *     }
   *
   * `next` is read once, as GetIterator reads it, and called on the iterator
   * at each step (a bound function is that call). The `closing` region runs
   * `close` before a `break` of the loop leaves it, before a `return` returns,
   * and, its own throws discarded, before a throw out of the body resumes
   * (IteratorClose with a throw completion); a `continue` and the body's end
   * go to the next step, and a done result leaves without it. `return`
   * absent (`undefined`) is not called; its result must be an object, the
   * TypeError IteratorClose throws otherwise being then impossible. Each part
   * has a claim site of its own: a token of the header or a run of them. */
  private protocolForOf(node: ts.ForOfStatement, list: ts.VariableDeclarationList,
      name: ts.Identifier, method: boolean): Stmt {
    const s = node.getStart(this.file);
    const p = this.token(s + "for".length, "(", node);
    const c = list.getStart(this.file);
    const [n0, n1] = this.span(name);
    const o = this.token(list.end, "of", node);
    const [e0, e1] = this.span(node.expression);
    const q = this.token(e1, ")", node);
    const end = node.end;
    const iterator = `%iterator@${s}`, next = `%next@${s}`, result = `%result@${s}`;
    const id = (pos: Span, name: string): Expr => ({ k: "id", pos, name });
    const iteratorAt = (): Expr => id([q, q + 1], iterator);
    const symbol = this.wellKnownIterator;
    if (symbol === null) this.fail(node, "a program's iterable needs the well-known `Symbol.iterator`, which the declarations do not list");
    const getIterator: Expr = { k: "invoke", pos: [o, e1], args: [],
      callee: { k: "read", pos: [o, o + "of".length], field: { symbol }, e: this.expr(node.expression) } };
    const bound: Expr = { k: "bindWithReceiver", pos: [s, q + 1], args: [],
      callee: { k: "read", pos: [p, q + 1], field: "next", e: iteratorAt() }, receiver: iteratorAt() };
    // The close's sites: the header's runs of tokens the steps do not use.
    const entries = [o, o + 1, q];
    const spans: Span[] = [[n0, e1], [s, end], [e0, q + 1], [o, q + 1], [c, q + 1], [p, e1]];
    const close = this.closeStatements(iteratorAt, `${s}`, {
      entry: () => entries.shift() ?? this.fail(node, "internal: the close's entries"),
      span: () => spans.shift() ?? this.fail(node, "internal: the close's sites"),
    }, method);
    const step: Stmt[] = [
      { k: "const", pos: [c, c + "const".length], bindings: [{ name: result, namePos: [c, c + "const".length],
        annot: null, init: { k: "apply", pos: [s, s + "for".length], callee: id([c, e1], next), args: [] } }] },
      { k: "if", pos: [c + 1, c + 2],
        cond: { k: "read", pos: [c, c + "const".length], field: "done", e: id([p, p + 1], result) },
        then: [{ k: "break", pos: [c + 2, c + 3], label: null }], else_: null },
      { k: "const", pos: [n0, n1], bindings: [{ name: this.local(name), namePos: [n0, n1], annot: null,
        init: { k: "read", pos: [n0, n1], field: "value", e: id([c, n1], result) } }] },
      { k: "closing", pos: [s + 1, s + 2], close, body: this.block(node.statement) },
    ];
    return { k: "block", pos: this.span(node), label: null, body: [
      { k: "const", pos: [s, s + "for".length], bindings: [
        { name: iterator, namePos: [s, s + "for".length], annot: null, init: getIterator },
        { name: next, namePos: [p, p + 1], annot: null, init: bound }] },
      { k: "while", pos: [p, end], cond: { k: "lit", pos: [s, p + 1], lit: { a: "booleanlit", v: "true" } },
        body: step, update: [] },
    ] };
  }

  /** Claim sites for the parts a lowering adds to the statement `within`:
   * the offsets from its start up to the next token after it at which no node
   * of it starts and that lie in no function nested in it, whose statements
   * have sites of their own. Each is an entry once (`entry`), and the spans
   * from them are expression sites (`span`); none is a source node's site. */
  private sites(within: Node): { entry(): number; span(): Span } {
    const text = this.file.text;
    let to = within.end;
    while (to < text.length && /\s/.test(text[to] ?? "")) to++;
    const free = freeOffsets(within, this.file);
    let entries = 0, from = 0, end = 0;
    return {
      entry: () => {
        const o = free[entries++];
        if (o === undefined) return this.fail(within, "too few claim sites in the statement for the iterator protocol it runs");
        return o;
      },
      span: () => {
        for (;;) {
          const a = free[from];
          if (a === undefined) return this.fail(within, "too few claim sites in the statement for the iterator protocol it runs");
          if (end === 0) end = a;
          if (++end <= to) return [a, end];
          from++;
          end = 0;
        }
      },
    };
  }

  /** GetIterator on a program's iterable, as `protocolForOf` does it: the
   * declarators `%iterator = iterable[Symbol.iterator](), %next =
   * %iterator.next.bind(%iterator)`, `next` read once and called on the
   * iterator at each step (`protocolStep`). */
  private protocolStart(iterable: Expr, site: { entry(): number; span(): Span }, tag: string, at: Node):
      { bindings: BindingAst[]; iterator: string; next: string; iteratorAt: () => Expr } {
    const iterator = `%iterator@${tag}`, next = `%next@${tag}`;
    const symbol = this.wellKnownIterator;
    if (symbol === null)
      return this.fail(at, "a program's iterable needs the well-known `Symbol.iterator`, which the declarations do not list");
    const iterAt = site.span();
    const iteratorAt = (): Expr => ({ k: "id", pos: iterAt, name: iterator });
    const call = site.span(), method = site.span(), bound = site.span(), nextRead = site.span();
    return {
      iterator, next, iteratorAt,
      bindings: [
        { name: iterator, namePos: call, annot: null, init: { k: "invoke", pos: call, args: [],
          callee: { k: "read", pos: method, field: { symbol }, e: iterable } } },
        { name: next, namePos: bound, annot: null, init: { k: "bindWithReceiver", pos: bound, args: [],
          callee: { k: "read", pos: nextRead, field: "next", e: iteratorAt() }, receiver: iteratorAt() } },
      ],
    };
  }

  /** One step of the protocol, `%next()`, bound to `result`, and the test of
   * its `done`, which leaves by `leave`: three statements, with their
   * entries. The value is `result`'s `value`, read by the caller next. */
  private protocolStep(next: string, result: string, leave: () => Stmt,
      site: { entry(): number; span(): Span }): { stmts: Stmt[]; value: () => Expr } {
    const nextAt = site.span();
    const e1 = site.entry();
    const call: Expr = { k: "apply", pos: site.span(), callee: { k: "id", pos: nextAt, name: next }, args: [] };
    const e2 = site.entry();
    const doneRead: Expr = { k: "read", pos: site.span(), field: "done", e: { k: "id", pos: site.span(), name: result } };
    const valueAt = site.span(), resultAt = site.span();
    return {
      stmts: [
        { k: "const", pos: [e1, e1 + 1], bindings: [{ name: result, namePos: call.pos, annot: null, init: call }] },
        { k: "if", pos: [e2, e2 + 1], cond: doneRead, then: [leave()], else_: null },
      ],
      value: () => ({ k: "read", pos: valueAt, field: "value", e: { k: "id", pos: resultAt, name: result } }),
    };
  }

  /** `switch (d) { clauses }`, as labeled blocks, one per clause, nested in
   * source order inside one for the whole switch. The innermost holds the
   * dispatch: it tests the discriminant with `===` against each case label
   * in source order, a match leaving the block of that label's clause, and
   * with every test failed leaves the block of `default`, or the switch's.
   * Each clause's statements follow its block's end, inside the next clause's
   * block, so a clause that completes runs on into the next one's statements,
   * as JavaScript falls through; a `break` leaves the switch's block. A
   * discriminant that is a name, or a field of a name, is read again at each
   * test, at the `case` keyword (the name of a field's object at its first
   * character), when every label is a literal or a name, since then nothing
   * between the tests writes and a field is a plain location; each test then
   * narrows the name, or the object's arms, as an `if` does. Any other is
   * evaluated first and bound to a name no source can spell. Every span is a node or a token: a test's `if`
   * begins at `case`, its read of the discriminant is at `case`, its `===`
   * at the clause's `:`, and its jump at the label; the jump to `default` is
   * at the keyword, the one to the switch's end at the clauses' `{`. The clauses
   * share one scope in JavaScript, so a name one declares directly must not
   * be read in another clause or in a label. */
  private switchStmt(node: ts.SwitchStatement): Stmt {
    const clauses = node.caseBlock.clauses;
    for (const c of clauses) {
      const declared = new Set<string>();
      const collect = (n: Node): void => {
        if (ts.isIdentifier(n)) declared.add(n.text);
        else n.forEachChild(collect);
      };
      for (const s of c.statements) {
        if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) collect(d.name);
        else if (ts.isClassDeclaration(s) && s.name) declared.add(s.name.text);
      }
      if (!declared.size) continue;
      const refers = (n: Node): Node | undefined =>
        ts.isIdentifier(n) && declared.has(n.text) ? n : n.forEachChild(refers);
      for (const other of clauses) {
        const at = (ts.isCaseClause(other) ? refers(other.expression) : undefined) ??
          (other === c ? undefined : other.statements.map(refers).find((n) => n));
        if (at) this.fail(at, "a name declared in one switch clause and read in another is outside the fragment");
      }
    }
    const unwrap = (e: Expression): Expression => (ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e);
    const plain = (e: Expression): boolean => {
      const u = unwrap(e);
      return ts.isIdentifier(u) || ts.isStringLiteral(u) || ts.isNumericLiteral(u) ||
        u.kind === ts.SyntaxKind.TrueKeyword || u.kind === ts.SyntaxKind.FalseKeyword ||
        u.kind === ts.SyntaxKind.NullKeyword ||
        (ts.isPrefixUnaryExpression(u) && u.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(u.operand));
    };
    const discriminant = unwrap(node.expression);
    const bound: Stmt[] = [];
    let name: string;
    const fieldOf = ts.isPropertyAccessExpression(discriminant) && !discriminant.questionDotToken &&
      ts.isIdentifier(discriminant.expression) &&
      !this.staticReads.has(this.span(discriminant.name).join(":"))
      ? { object: this.local(discriminant.expression), field: discriminant.name.text } : null;
    const reread = clauses.every((c) => !ts.isCaseClause(c) || plain(c.expression));
    if (ts.isIdentifier(discriminant) && reread) name = this.local(discriminant);
    else if (fieldOf && reread) name = fieldOf.object;
    else {
      name = `%switch@${node.getStart(this.file)}%`;
      const at = this.span(node.expression);
      bound.push({ k: "const", pos: at, bindings: [{ name, namePos: at, annot: null, init: this.expr(node.expression) }] });
    }
    const end = switchLabel(node, this.file);
    const label = (c: ts.CaseOrDefaultClause): string => `%case@${c.getStart(this.file)}%`;
    const dispatch: Stmt[] = [];
    let fallback: Stmt | null = null;
    for (const c of clauses) {
      const start = c.getStart(this.file);
      if (!ts.isCaseClause(c)) {
        fallback = { k: "break", pos: [start, start + "default".length], label: label(c) };
        continue;
      }
      const colon = this.token(c.expression.end, ":", c);
      dispatch.push({ k: "if", pos: [start, c.expression.end],
        cond: { k: "bin", pos: [colon, colon + 1], op: "===",
          l: fieldOf && reread
            ? { k: "read", pos: [start, start + "case".length], field: fieldOf.field,
                e: { k: "id", pos: [start, start + 1], name } }
            : { k: "id", pos: [start, start + "case".length], name },
          r: this.expr(c.expression) },
        then: [{ k: "break", pos: this.span(c.expression), label: label(c) }], else_: null });
    }
    const open = node.caseBlock.getStart(this.file);
    dispatch.push(fallback ?? { k: "break", pos: [open, open + 1], label: end });
    const body = clauses.reduce<Stmt[]>((inner, c) =>
      [{ k: "block", pos: this.span(c), label: label(c), body: inner }, ...this.statements(c.statements)], dispatch);
    return { k: "block", pos: this.span(node), label: end, body: [...bound, ...body] };
  }

  /** `try { … } catch (e) { … } finally { … }`. The caught value is
   * `unknown`, the only annotation admitted: anything may be thrown. The
   * finalizer runs on every way out of the body and the handler, which the
   * lowering states by running it on each (`SourceExtraction`). */
  private tryStmt(node: ts.TryStatement): Stmt {
    const handler = node.catchClause;
    let param: { name: string; namePos: Span } | null = null;
    const d = handler?.variableDeclaration;
    if (d) {
      if (!ts.isIdentifier(d.name)) this.fail(d, "destructuring is outside the fragment");
      if (d.type && d.type.kind !== ts.SyntaxKind.UnknownKeyword)
        this.fail(d.type, "a caught value is `unknown`");
      if (d.name.text === "undefined") this.fail(d, "shadowing undefined is outside the fragment");
      param = { name: this.local(d.name), namePos: this.span(d.name) };
    }
    return {
      k: "try",
      pos: this.span(node),
      body: this.statements(node.tryBlock.statements),
      handler: handler ? { param, body: this.statements(handler.block.statements) } : null,
      finalizer: node.finallyBlock ? this.statements(node.finallyBlock.statements) : null,
    };
  }

  /** Whether a statement never completes normally: a jump, or a list or both
   * arms of an `if` that reach one. A loop may complete. */
  private abrupt(s: Statement): boolean {
    return ts.isReturnStatement(s) || ts.isBreakStatement(s) || ts.isContinueStatement(s) ||
      ts.isThrowStatement(s) ||
      (ts.isBlock(s) && s.statements.some((t) => this.abrupt(t))) ||
      (ts.isIfStatement(s) && !!s.elseStatement && this.abrupt(s.thenStatement) && this.abrupt(s.elseStatement)) ||
      // A `try` completes through its body or handler, then its `finally`.
      (ts.isTryStatement(s) && ((!!s.finallyBlock && this.abrupt(s.finallyBlock)) ||
        (this.abrupt(s.tryBlock) && (!s.catchClause || this.abrupt(s.catchClause.block)))));
  }

  stmt(node: Statement): Stmt {
    if (ts.isExpressionStatement(node))
      return {
        k: "effect",
        pos: this.span(node),
        e: this.expr(node.expression),
      };

    if (ts.isReturnStatement(node)) {
      const start = node.getStart(this.file);
      const keyword: Span = [start, start + "return".length];
      // A bare `return` returns `undefined`: the literal, at the keyword. In
      // an async body it settles the call's promise as completing does:
      // `return %AsyncComplete%()`.
      if (!node.expression)
        return {
          k: "return",
          pos: this.span(node),
          e: this.asyncBody
            ? this.intrinsic(asyncCompleteName, this.span(node), keyword, [])
            : { k: "lit", pos: keyword, lit: { a: "undefined" } },
        };
      const e = this.expr(node.expression);
      // In an async body, `return e` is `return %AsyncReturn%(e)`, the call
      // spanning the statement, the intrinsic read at the keyword.
      return {
        k: "return",
        pos: this.span(node),
        e: this.asyncBody
          ? this.intrinsic(asyncReturnName, this.span(node), keyword, [e])
          : e,
      };
    }

    if (ts.isVariableStatement(node)) return this.declarations(node.declarationList, node);

    if (ts.isBreakStatement(node) || ts.isContinueStatement(node)) {
      if (node.label)
        this.fail(node, "only unlabeled loop transfers are supported");
      const target = jumpTarget(node);
      if (!target)
        this.fail(node, "break or continue outside a supported loop");
      // A `break` out of a `switch` goes to the end of the block it is
      // lowered to (`switchStmt`).
      if (ts.isBreakStatement(node))
        return { k: "break", pos: this.span(node),
          label: ts.isSwitchStatement(target) ? switchLabel(target, this.file) : null };
      return { k: "continue", pos: this.span(node) };
    }
    return this.controlStmt(node);
  }

  /** A `let` or `const` declaration list, the statement `at` spans: a
   * variable statement, or a `for` loop's initializer. */
  private declarations(list: ts.VariableDeclarationList, at: Node): Stmt {
    // `var` is function-scoped and hoisted, so it is not this binding form.
    if (!(list.flags & ts.NodeFlags.Const) && !(list.flags & ts.NodeFlags.Let))
      this.fail(at, "`var` is outside the fragment");
    // A `let` statement whose bindings are all initialized and nothing
    // assigns is a `const`: each binding holds its initial value throughout,
    // so reading it reads that value, as a `const`'s read does.
    const mutable = !(list.flags & ts.NodeFlags.Const) && !(ts.isVariableStatement(at) && this.neverAssigned(list));
    const kindWord = mutable ? "let" : "const";
    if (
      list.declarations.some(
        (d) =>
          ts.isObjectBindingPattern(d.name) ||
          ts.isArrayBindingPattern(d.name),
      )
    )
      return this.patternStmt(list, at, mutable);
    // A declaration list binds its declarators left to right, each
    // initializer seeing the earlier bindings, under the statement's one
    // entry. Each declarator is gated on its own terms.
    const bindings: BindingAst[] = list.declarations.map((d) => {
      if (d.name.kind !== ts.SyntaxKind.Identifier)
        this.fail(d, "destructuring is outside the fragment");
      if (d.name.text === "undefined")
        this.fail(d, "shadowing undefined is outside the fragment");
      // `let x: T;` binds `undefined` where it is declared: it is
      // `let x: T | undefined = undefined`, the cell's contract admitting
      // the value it starts with. A read of it before an assignment is
      // `undefined`, and a read after one is at `T` only where Lean proves
      // the cell's current contents are, as for any other cell. Without an
      // annotation there is no contract (TypeScript's evolving `any`).
      if (!d.initializer) {
        if (!mutable || !d.type)
          this.fail(d, `a \`${kindWord}\` needs an initializer`);
        return {
          name: this.local(d.name),
          namePos: this.span(d.name),
          annot: this.optionalTypeOf(d.type, d),
          init: { k: "lit", pos: this.span(d), lit: { a: "undefined" } },
        };
      }
      // For `let`, the storage contract is what every later assignment is
      // checked against. Written, it is the annotation; unwritten, the
      // producer states one for the binding and the adapter checks that,
      // rather than this taking the initializer's type for the contract.
      return {
        name: this.local(d.name),
        namePos: this.span(d.name),
        annot: d.type ? this.typeOf(d.type) : null,
        init: this.expr(d.initializer),
      };
    });
    if (mutable) return { k: "let", pos: this.span(at), bindings };
    return { k: "const", pos: this.span(at), bindings };
  }

  /** Whether a `let` list's bindings are all initialized and none is
   * written in the scope it binds them in: no assignment, compound or
   * logical assignment, update or destructuring assignment names one. A
   * write is found by the name the fragment gives the binding (`local`), so
   * a same-named binding elsewhere in that scope keeps the list a `let`. */
  private neverAssigned(list: ts.VariableDeclarationList, loopHead = false): boolean {
    const [first] = list.declarations;
    // A loop head's binding is bound by each iteration, not by an initializer.
    if (!first || (!loopHead && list.declarations.some((d) => !d.initializer))) return false;
    const names = new Set<string>();
    const bind = (n: ts.BindingName): void => {
      if (ts.isIdentifier(n)) names.add(this.local(n));
      else for (const e of n.elements) if (!ts.isOmittedExpression(e) && e.name) bind(e.name);
    };
    for (const d of list.declarations) bind(d.name);
    const targets = (e: Node): boolean => {
      while (ts.isParenthesizedExpression(e)) e = e.expression;
      if (ts.isIdentifier(e)) return names.has(this.local(e));
      if (ts.isArrayLiteralExpression(e)) return e.elements.some(targets);
      if (ts.isObjectLiteralExpression(e)) return e.properties.some((p) =>
        ts.isShorthandPropertyAssignment(p) ? ts.isIdentifier(p.name) && names.has(this.local(p.name))
          : ts.isPropertyAssignment(p) ? targets(p.initializer)
          : ts.isSpreadAssignment(p) ? targets(p.expression) : false);
      if (ts.isSpreadElement(e)) return targets(e.expression);
      if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return targets(e.left);
      return false;
    };
    const writes = (n: Node): boolean => {
      if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
          n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && targets(n.left)) return true;
      if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
          (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
          targets(n.operand)) return true;
      if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer) &&
          targets(n.initializer)) return true;
      return !!n.forEachChild((c) => writes(c) || undefined);
    };
    return !writes(bindingScope(first));
  }

  /** Loops, branches, blocks, `switch`, `try` and `throw`. */
  private controlStmt(node: Statement): Stmt {
    if (ts.isWhileStatement(node))
      return {
        k: "while",
        pos: this.span(node),
        cond: this.expr(node.expression),
        body: this.block(node.statement),
        update: [],
      };

    if (ts.isForStatement(node)) return this.forStmt(node);
    if (ts.isForInStatement(node)) return this.forInStmt(node);
    if (ts.isSwitchStatement(node)) return this.switchStmt(node);
    if (ts.isTryStatement(node)) return this.tryStmt(node);
    // `throw e`: `e`, then a throw of its value, which leaves the function
    // unless a `try` around it catches it.
    if (ts.isThrowStatement(node))
      return { k: "throw", pos: this.span(node), e: this.expr(node.expression) };

    // `{ … }`: its statements in a scope of their own.
    if (ts.isBlock(node))
      return { k: "block", pos: this.span(node), label: null, body: this.statements(node.statements) };

    // `for (const x of e) body`: one immutable binding per iteration. The
    // iterable is the argument of the iteration intrinsic that steps its
    // iterator (`intrinsics.mts`), picked by TypeScript's type of it:
    // `%Iterate%` for an array, and the one of a string, a `Set`, a `Map` or
    // a host collection iterator. Lean checks the call at its signature.
    if (ts.isForOfStatement(node)) {
      if (node.awaitModifier)
        this.fail(node, "`for await` is outside the fragment");
      // A `let` nothing assigns is a `const`, as a statement's is: each
      // iteration binds it afresh, and nothing changes it after.
      const list = node.initializer;
      if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1 ||
          !(list.flags & ts.NodeFlags.Const || (list.flags & ts.NodeFlags.Let && this.neverAssigned(list, true))))
        this.fail(node, "a `for...of` loop declares one `const` binding, or a `let` nothing assigns");
      const d = list.declarations[0];
      if (!ts.isIdentifier(d.name))
        this.fail(d, "destructuring is outside the fragment");
      if (d.type || d.initializer)
        this.fail(d, "a `for...of` binding takes the element's type");
      if (d.name.text === "undefined")
        this.fail(d, "shadowing undefined is outside the fragment");
      const iterate = this.iterations.get(this.span(node.expression).join(":")) ?? iterateName;
      if (iterate === "client-unclosable")
        this.fail(node.expression, UNCLOSABLE);
      if (iterate === "client" || iterate === "client-method")
        return this.protocolForOf(node, list, d.name, iterate === "client-method");
      return {
        k: "forOf",
        pos: this.span(node),
        name: this.local(d.name),
        namePos: this.span(d.name),
        iterate,
        iterable: this.expr(node.expression),
        body: this.block(node.statement),
      };
    }

    // `else if (c) s` is `else { if (c) s }`: an unbraced arm is the one
    // statement its block would hold (`block`).
    if (ts.isIfStatement(node)) {
      return {
        k: "if",
        pos: this.span(node),
        cond: this.expr(node.expression),
        then: this.block(node.thenStatement),
        else_: node.elseStatement ? this.block(node.elseStatement) : null,
      };
    }

    this.fail(
      node,
      `statement outside the fragment (${ts.SyntaxKind[node.kind]})`,
    );
  }

  /* --------------------------------------------------------- functions -- */

  functionDecl(node: FunctionDeclaration): FunctionAst {
    if (!node.name) this.fail(node, "anonymous function");
    if (node.name.text === "undefined")
      this.fail(node, "shadowing undefined is outside the fragment");
    if (node.modifiers?.some(modifier => modifier.kind !== ts.SyntaxKind.ExportKeyword &&
        modifier.kind !== ts.SyntaxKind.AsyncKeyword))
      this.fail(
        node,
        "only the export and async modifiers are admitted on a source function",
      );
    if (node.asteriskToken)
      this.fail(node, GENERATOR);
    const isAsync = !!node.modifiers?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword);
    if (!node.body) this.fail(node, "a function must have a body");
    const prologue = this.useStrict(node.body.statements);
    if (
      prologue.strict &&
      node.parameters.some((p) => p.initializer || p.dotDotDotToken || !ts.isIdentifier(p.name))
    )
      this.fail(node, '"use strict" beside non-simple parameters');
    const outerStrict = this.strict;
    this.strict = outerStrict || prologue.strict;
    // A declaration is the entry point, not a callable of the fragment: a
    // `this: T` parameter is one more input assumed at its annotation, like
    // every other parameter, and the body's `this` is that parameter.
    const head = node.parameters[0];
    const receiverParam =
      !!head && ts.isIdentifier(head.name) && head.name.text === "this";
    if (
      receiverParam &&
      (!head.type || head.questionToken || head.dotDotDotToken)
    )
      this.fail(head, "a receiver needs a required type annotation");
    const outerReceiverMode = this.receiverMode;
    const outerAsync = this.asyncBody;
    this.receiverMode = receiverParam
      ? this.strict
        ? "strict"
        : "sloppy"
      : null;
    const typeParams = this.enterTypeParams(node.typeParameters, undefined, true);
    try {
      this.asyncBody = isAsync;
      const { retType, parameterTypes } = this.headerTypes(() => ({
        retType: this.typeOf(node.type),
        parameterTypes: node.parameters.map(p => p.dotDotDotToken ? this.moduleRestType(p, node)
          : p.questionToken || p.initializer ? this.optionalTypeOf(p.type, p)
          : this.typeOf(p.type, p)),
      }));
      // A parameter written as a pattern or with a default binds a hidden
      // name, which the caller's argument initializes; a `destructure` over
      // it, first in the body in parameter order, binds the source's names,
      // the default replacing an undefined argument. JavaScript evaluates
      // them there too, in order, before the body.
      const names = new Set<string>();
      const bindings: Stmt[] = [];
      const params = node.parameters.map((p, i) => {
        if (ts.isIdentifier(p.name) && p.name.text === "undefined")
          this.fail(p, "shadowing undefined is outside the fragment");
        if (
          !p.questionToken &&
          !p.initializer &&
          !p.dotDotDotToken &&
          node.parameters.indexOf(p) > firstOptional(node.parameters)
        )
          this.fail(p, "a required parameter cannot follow an optional one");
        if (p.dotDotDotToken) {
          if (p.questionToken) this.fail(p, "a rest parameter is not optional");
          if (p !== node.parameters[node.parameters.length - 1])
            this.fail(p, "a rest parameter must be the last one");
          if (!ts.isIdentifier(p.name))
            this.fail(p, "a rest parameter pattern is outside the fragment");
        }
        if (ts.isIdentifier(p.name) && !p.initializer) {
          names.add(p.name.text);
          return {
            name: this.local(p.name),
            pos: this.span(p.name),
            type: parameterTypes[i] ?? this.fail(p, "missing parameter contract"),
            ...(p.dotDotDotToken ? { rest: true as const } : {}),
          };
        }
        const hidden = parameterName(i);
        const at = this.span(p.name);
        bindings.push({
          k: "destructure",
          pos: this.span(p),
          target: this.pattern(p.name, names),
          default_: p.initializer ? this.expr(p.initializer) : null,
          init: { k: "id", pos: at, name: hidden },
        });
        return {
          name: hidden,
          pos: at,
          // A caller may pass `undefined` where there is a default.
          type: parameterTypes[i] ?? this.fail(p, "missing parameter contract"),
        };
      });
      this.initializedBefore(node, params.map((p): [PatternAst, Expr | null] => {
        const b = bindings.find((st) => st.k === "destructure" && st.init.k === "id" && st.init.name === p.name);
        return b?.k === "destructure" ? [b.target, b.default_] : [{ k: "name", name: p.name, pos: p.pos }, null];
      }));
      const body = [...bindings,
        ...this.statements(node.body.statements.filter((s) => !prologue.skip.has(s)))];
      return {
        name: node.name.text,
        namePos: this.span(node.name),
        typeParams,
        params,
        retType,
        body: isAsync ? this.asyncCompletion(node.body, body) : body,
        strict: this.strict,
      };
    } finally {
      this.leaveTypeParams();
      this.strict = outerStrict;
      this.receiverMode = outerReceiverMode;
      this.asyncBody = outerAsync;
    }
  }
}

/** A member of one of the file's enums: its name, its declaration's spans,
 * and its value as TypeScript computes it. */
type EnumMember = { name: string; node: ts.EnumMember; span: Span; nameSpan: Span; init: Span | null;
  value: string | number | null };
/** An enum: where its declaration ends, whether it is ambient (`declare
 * enum`, not `const`), and its members, each value `undefined` until the
 * declaration graph reports it. */
type EnumInfo = { end: number; ambient: boolean;
  members: (Omit<EnumMember, "value"> & { value: string | number | undefined })[] };

/** Whether an element access is written rather than read: the target of an
 * assignment, a compound assignment or an update, or `delete`'s operand. */
function writtenElement(node: ts.ElementAccessExpression): boolean {
  let at: Node = node;
  while (at.parent && ts.isParenthesizedExpression(at.parent)) at = at.parent;
  const parent = at.parent;
  if (!parent) return false;
  if (ts.isBinaryExpression(parent) && parent.left === at &&
      parent.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      parent.operatorToken.kind <= ts.SyntaxKind.LastAssignment) return true;
  if ((ts.isPrefixUnaryExpression(parent) || ts.isPostfixUnaryExpression(parent)) &&
      (parent.operator === ts.SyntaxKind.PlusPlusToken || parent.operator === ts.SyntaxKind.MinusMinusToken))
    return true;
  return ts.isDeleteExpression(parent);
}

/** Whether a function's type parameter is named anywhere in it but at
 * `except`: its signature, its body, a nested function's (one declaring a
 * type parameter of the same name hides it there). */
function typeParameterMentioned(node: FunctionDeclaration, parameter: TypeParameterDeclaration,
    except: Node): boolean {
  const name = parameter.name.text;
  const visit = (n: Node): boolean => {
    if (n === except || n === parameter) return false;
    if (n !== node && ts.isFunctionLikeDeclaration(n) &&
        n.typeParameters?.some((tp: TypeParameterDeclaration) => tp.name.text === name)) return false;
    if (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) && n.typeName.text === name) return true;
    if (ts.isTypeQueryNode(n)) return false;
    return n.forEachChild(visit) ?? false;
  };
  return visit(node);
}

/** `Object.assign(arrow, literal)`: the callable form, a function with
 * properties. */
function callableAssign(node: Node): node is ts.CallExpression {
  return ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
    ts.isIdentifier(node.expression.expression) && node.expression.expression.text === "Object" &&
    node.expression.name.text === "assign" && node.arguments.length === 2 &&
    ts.isArrowFunction(node.arguments[0]) && ts.isObjectLiteralExpression(node.arguments[1]);
}

/** The key of `k in o`, its parentheses dropped. */
function inKey(node: ts.BinaryExpression): Expression {
  let key: Expression = node.left;
  while (ts.isParenthesizedExpression(key)) key = key.expression;
  return key;
}

/** Whether `within` writes a binding spelled `name`: an assignment, a
 * compound or logical one, an update, a destructuring assignment or a
 * `for...of`/`for...in` head naming it. By spelling, so a binding of
 * another scope with the same name counts too. */
function writesName(within: Node, name: string): boolean {
  const targets = (e: Node): boolean => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) return e.text === name;
    if (ts.isArrayLiteralExpression(e)) return e.elements.some(targets);
    if (ts.isObjectLiteralExpression(e)) return e.properties.some((p) =>
      ts.isShorthandPropertyAssignment(p) ? ts.isIdentifier(p.name) && p.name.text === name
        : ts.isPropertyAssignment(p) ? targets(p.initializer)
        : ts.isSpreadAssignment(p) ? targets(p.expression) : false);
    if (ts.isSpreadElement(e)) return targets(e.expression);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return targets(e.left);
    return false;
  };
  const visit = (n: Node): boolean => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && targets(n.left)) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        targets(n.operand)) return true;
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer) &&
        targets(n.initializer)) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(within);
}

/** Whether running `node` may run code or write a property: a call, a
 * construction (a class's definition, whose static parts run, among them),
 * a tagged template, `await` or `yield` (other code runs meanwhile), an
 * iteration (a `for...of`, an array spread or pattern, which may step a
 * program's iterator), `instanceof` (which may call a static
 * `[Symbol.hasInstance]`), `delete`, a template (whose conversion of an
 * object calls its `toString`), or a write other than to a binding. A
 * function written there runs nothing until called, which is a call. The
 * implicit conversions of an object that run its code elsewhere (`o + ""`,
 * a relational comparison) are refused by the model (DESIGN.md, "Refused on
 * principle"), and a read runs none: an object holds data properties only. */
function runsCodeOrWrites(node: Node): boolean {
  const target = (e: Node): Node => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    return e;
  };
  const visit = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return false;
    if (ts.isCallExpression(n) || ts.isNewExpression(n) || ts.isTaggedTemplateExpression(n) ||
        ts.isAwaitExpression(n) || ts.isYieldExpression(n) || ts.isForOfStatement(n) || ts.isSpreadElement(n) ||
        ts.isArrayBindingPattern(n) || ts.isDeleteExpression(n) || ts.isTemplateExpression(n) ||
        ts.isClassDeclaration(n) || ts.isClassExpression(n)) return true;
    if (ts.isBinaryExpression(n) && (n.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword ||
        (n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
         n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && !ts.isIdentifier(target(n.left))))) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        !ts.isIdentifier(target(n.operand))) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(node);
}

/** The reads of the entry a `for...in` step visited, `P[k]` in
 * `for (const k in P) { … }` with `P` the loop's operand spelled again (a
 * name, or a chain of named reads from one) and `k` its key: each such read
 * in the statements the body starts with that run no code and write no
 * property (`runsCodeOrWrites`), outside the functions they define, and the
 * read that is the whole initializer, under a non-null assertion or not, of
 * the first declarator of the declaration that follows them. Each is the
 * entry the step visited, the value `P`'s object holds under `k` at the step:
 * nothing that ran since the step can change it, and `P` still denotes the
 * object the loop enumerates, since no code in the outermost function holding
 * the loop (the file, for a loop at the top level) writes `P`'s name and,
 * where `P` reads fields, running the loop's body runs no code and writes no
 * property, so no iteration changes what the chain finds. No declaration in
 * those statements, nor any of the body's own, spells the key's or `P`'s
 * name, which a read would then name instead. Empty where there is none. */
function forInEntryReads(node: ts.ForInStatement): ts.ElementAccessExpression[] {
  const list = node.initializer;
  if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1) return [];
  const key = list.declarations[0]?.name;
  if (!key || !ts.isIdentifier(key) || !ts.isBlock(node.statement)) return [];
  const samePath = (a: Expression, b: Expression): Identifier | null =>
    ts.isIdentifier(a) && ts.isIdentifier(b) ? (a.text === b.text ? a : null)
    : ts.isPropertyAccessExpression(a) && ts.isPropertyAccessExpression(b) && !a.questionDotToken &&
      !b.questionDotToken && ts.isIdentifier(a.name) && ts.isIdentifier(b.name) && a.name.text === b.name.text
      ? samePath(a.expression, b.expression) : null;
  const rootOf = (e: Expression): Identifier | null => ts.isIdentifier(e) ? e
    : ts.isPropertyAccessExpression(e) && !e.questionDotToken && ts.isIdentifier(e.name) ? rootOf(e.expression) : null;
  const root = rootOf(node.expression);
  if (!root || root.text === key.text) return [];
  const names = new Set([key.text, root.text]);
  const entry = (e: Node): e is ts.ElementAccessExpression =>
    ts.isElementAccessExpression(e) && !e.questionDotToken && ts.isIdentifier(e.argumentExpression) &&
    e.argumentExpression.text === key.text && samePath(e.expression, node.expression) !== null;
  // A declaration spelling the key's or the root's name, outside the
  // functions a statement defines (whose bodies run later, if at all).
  const shadows = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n)) return false;
    if (ts.isFunctionDeclaration(n) || ts.isClassDeclaration(n)) return !!n.name && names.has(n.name.text);
    if ((ts.isVariableDeclaration(n) || ts.isBindingElement(n)) && n.name && ts.isIdentifier(n.name) &&
        names.has(n.name.text)) return true;
    return !!n.forEachChild((c) => shadows(c) || undefined);
  };
  // The body's own declarations bind from its start (a `let` or `const` in
  // its temporal dead zone until its declaration runs).
  for (const s of node.statement.statements)
    if ((ts.isVariableStatement(s) || ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && shadows(s)) return [];
  const reads: ts.ElementAccessExpression[] = [];
  const collect = (n: Node): void => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return;
    if (entry(n) && !writtenElement(n)) reads.push(n);
    n.forEachChild(collect);
  };
  for (const s of node.statement.statements) {
    if (!runsCodeOrWrites(s)) {
      if (shadows(s)) return [];
      collect(s);
      continue;
    }
    const [declaration] = ts.isVariableStatement(s) ? s.declarationList.declarations : [];
    let read: Expression | undefined = declaration?.initializer;
    while (read && ts.isParenthesizedExpression(read)) read = read.expression;
    if (read && ts.isNonNullExpression(read)) read = read.expression;
    if (read && entry(read)) reads.push(read);
    break;
  }
  if (!reads.length) return [];
  // A binding declared in a function is written only there; one declared at
  // the top level, only at the top level or in a function, all in the file.
  let scope: Node | undefined;
  let file: Node = node;
  for (let at: Node | undefined = node.parent; at; at = at.parent) {
    if (ts.isFunctionLikeDeclaration(at)) scope = at;
    file = at;
  }
  if (writesName(scope ?? file, root.text)) return [];
  if (!ts.isIdentifier(node.expression) && runsCodeOrWrites(node.statement)) return [];
  return reads;
}

/** The module constant holding the value of member `member` of enum `name`
 * where that value is known only at run time (`enumStmt`). */
const enumMemberName = (name: string, member: string): string => `%${name}.${member}%`;

/** An enum member's value as a literal expression. */
function literalExpr(value: string | number, pos: Span): Expr {
  return typeof value === "string"
    ? { k: "lit", pos, lit: { a: "stringlit", v: value } }
    : { k: "lit", pos, lit: { a: "numberlit", v: numberText(value) } };
}

/* ------------------------------------------------------------- parsing -- */

/**
 * The whole file, or a gate rejection. A rejection is an Error whose message
 * begins "gate: ", which is what the command writes to stderr, so a caller and
 * the command report one wording.
 *
 * `carriesContext` is for a caller that assembled the file itself and put
 * declarations beside the function it is asking about — the coverage run does, so
 * that a function is typed with the names its own file declares rather than
 * failing for what extracting it left behind. Those declarations are then not
 * the subject: they are skipped rather than rejected, and nothing about them
 * is verified. A type they introduce still has to be sayable in a claim, so a
 * function that depends on one fails on that claim, in its own words.
 */
/** The name the fragment gives a local that shadows a binding of an
 * enclosing scope: its spelling and where it is declared, which no source
 * binding can spell. */
function shadowName(id: Identifier, source: SourceFile): string {
  const { line, character } = source.getLineAndCharacterOfPosition(id.getStart(source));
  return `${id.text}@${line + 1}:${character + 1}`;
}

/** The scope a value declaration binds its name in, JavaScript's: a
 * parameter its function's, a `let`, `const`, class or function declaration
 * its block's (a `switch`'s clauses sharing one), a `for` head's binding the
 * loop's, a `var` its function's, a caught value its `catch` clause's, a
 * named function or class expression its own. */
function bindingScope(node: Node): Node {
  const block = (n: Node): Node => (ts.isCaseClause(n) || ts.isDefaultClause(n)) && n.parent ? n.parent : n;
  const functionOf = (n: Node): Node => {
    let at: Node | undefined = n.parent;
    while (at && !ts.isFunctionLikeDeclaration(at) && !ts.isSourceFile(at)) at = at.parent;
    return at ?? n;
  };
  if (ts.isBindingElement(node)) {
    let at: Node | undefined = node.parent;
    while (at && !ts.isVariableDeclaration(at) && !ts.isParameterDeclaration(at)) at = at.parent;
    return at ? bindingScope(at) : node;
  }
  if (ts.isParameterDeclaration(node)) return node.parent ?? node;
  if (ts.isVariableDeclaration(node)) {
    const list = node.parent;
    if (!list || ts.isCatchClause(list)) return list ?? node;
    if (!(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) return functionOf(node);
    const holder = list.parent;
    if (!holder) return list;
    if (ts.isForStatement(holder) || ts.isForOfStatement(holder) || ts.isForInStatement(holder)) return holder;
    return holder.parent ? block(holder.parent) : holder;
  }
  if (ts.isFunctionExpression(node) || ts.isClassExpression(node)) return node;
  return node.parent ? block(node.parent) : node;
}

/** The file's local value bindings that shadow a binding of an enclosing
 * scope, by the span of their name: a declaration whose name another
 * declaration binds in a scope enclosing its own (a named function or class
 * expression's own name encloses its parameters). */
function shadowingLocals(source: SourceFile): Map<string, Identifier> {
  const declared: { id: Identifier; scope: Node; own: boolean }[] = [];
  const visit = (node: Node): void => {
    if (ts.isTypeNode(node) || ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) return;
    const name = nameOf(node);
    if ((ts.isParameterDeclaration(node) || ts.isVariableDeclaration(node) || ts.isBindingElement(node) ||
         ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node) || ts.isEnumDeclaration(node) ||
         ts.isFunctionExpression(node) || ts.isClassExpression(node) || ts.isImportSpecifier(node) ||
         ts.isNamespaceImport(node) || ts.isImportClause(node)) &&
        name && ts.isIdentifier(name) && name.text !== "this")
      declared.push({ id: name, own: ts.isFunctionExpression(node) || ts.isClassExpression(node),
        scope: ts.isImportSpecifier(node) || ts.isNamespaceImport(node) || ts.isImportClause(node)
          ? source : bindingScope(node) });
    node.forEachChild(visit);
  };
  visit(source);
  const encloses = (outer: Node, inner: Node): boolean => {
    for (let at: Node | undefined = inner.parent; at; at = at.parent) if (at === outer) return true;
    return false;
  };
  const found = new Map<string, Identifier>();
  for (const d of declared)
    if (declared.some(o => o !== d && o.id.text === d.id.text &&
        (encloses(o.scope, d.scope) || (o.scope === d.scope && o.own && !d.own))))
      found.set(`${d.id.getStart(source)}:${d.id.end}`, d.id);
  return found;
}

export function parseFile(file: string, carriesContext = false,
  tsconfigPath?: string, resolutionFile = file,
  seen?: (diagnostic: SeenDiagnostic) => void): Ast {
  const absolute = resolve(file);
  const text = readFileSync(absolute, "utf8");
  const source = openFile(absolute, text);
  const gate = new Gate(source);
  const aliasNodes: TypeAliasDeclaration[] = [];
  const interfaceNodes: InterfaceDeclaration[] = [];
  const classNodes: ClassDeclaration[] = [];
  const fnNodes: FunctionDeclaration[] = [];
  const importNodes: ImportDeclaration[] = [];
  const enumNodes: ts.EnumDeclaration[] = [];
  // Top-level code other than declarations: the module's initialization, run
  // once, in order, after its function declarations are instantiated.
  const initNodes: Statement[] = [];
  // The names ambient declarations bind, `declare function f`: values the
  // declaration graph reads at their declared types.
  const ambientNames: Identifier[] = [];
  const ambient = (s: FunctionDeclaration | ClassDeclaration | VariableStatement): boolean =>
    !!s.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword);
  const topStatement = (n: Node): Node => n.parent && !ts.isSourceFile(n.parent) ? topStatement(n.parent) : n;
  // A "use strict" directive prologue makes the whole file strict.
  const prologue = gate.useStrict(source.statements);
  gate.strict = prologue.strict;
  // A direct `eval` runs a string as code in the caller's scope, where it may
  // read and write any local; sloppy code may rebind `eval` and `arguments`.
  const evalForms = (n: Node): void => {
    if (ts.isTypeNode(n)) return;
    if (ts.isCallExpression(n)) {
      let callee: Expression = n.expression;
      while (ts.isParenthesizedExpression(callee)) callee = callee.expression;
      if (ts.isIdentifier(callee) && callee.text === "eval")
        gate.fail(n, "a direct `eval` call runs a string as code in the caller's scope, which may read and write any of its bindings");
    }
    const name = nameOf(n);
    if ((ts.isParameterDeclaration(n) || ts.isVariableDeclaration(n) || ts.isBindingElement(n) ||
         ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isClassDeclaration(n) ||
         ts.isClassExpression(n)) && name && ts.isIdentifier(name) &&
        (name.text === "eval" || name.text === "arguments"))
      gate.fail(n, `a binding named \`${name.text}\`: sloppy code gives the name a meaning of its own (a direct eval, the arguments object)`);
    n.forEachChild(evalForms);
  };
  evalForms(source);
  for (const s of source.statements) {
    if (prologue.skip.has(s)) continue;
    if (ts.isTypeAliasDeclaration(s)) aliasNodes.push(s);
    else if (ts.isInterfaceDeclaration(s) && !carriesContext) interfaceNodes.push(s);
    // A class declaration declares its instance type, and its value is part of
    // the module's initialization, in order: classes are not hoisted.
    else if (ts.isClassDeclaration(s) && !carriesContext) {
      classNodes.push(s);
      // A `declare class` states its instance type and its constructor's
      // signature; nothing defines it here, so it runs nothing.
      if (ambient(s)) ambientNames.push(...(s.name ? [s.name] : []));
      else initNodes.push(s);
    }
    // `declare function f(...): T;`, once per overload: the value is assumed
    // at its declared signatures, like an import's. It runs nothing.
    else if (ts.isFunctionDeclaration(s) && ambient(s) && !carriesContext) {
      if (s.name && !ambientNames.some(n => n.text === s.name?.text)) ambientNames.push(s.name);
    }
    else if (ts.isFunctionDeclaration(s)) fnNodes.push(s);
    else if (ts.isImportDeclaration(s) && !carriesContext) importNodes.push(s);
    // An enum is a module constant bound to its object where it is written;
    // a `const enum` runs nothing, its reads being its members' values. An
    // ambient enum runs nothing either: its object is the environment's,
    // which the declaration graph lists among the values.
    else if (ts.isEnumDeclaration(s) && !carriesContext) {
      const declared = !!s.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword);
      const inlined = s.modifiers?.some(m => m.kind === ts.SyntaxKind.ConstKeyword);
      enumNodes.push(s);
      gate.enums.set(s.name.text, { end: s.end, ambient: declared && !inlined, members: s.members.map(m => ({
        name: ts.isIdentifier(m.name) || ts.isStringLiteral(m.name) ? m.name.text
          : gate.fail(m, "an enum member needs a plain name"),
        node: m, span: gate.span(m), nameSpan: gate.span(m.name),
        init: m.initializer ? gate.span(m.initializer) : null, value: undefined })) });
      if (!inlined && !declared) initNodes.push(s);
    }
    else if (carriesContext) continue;
    // `;` is nothing, at the top level as in a body.
    else if (ts.isEmptyStatement(s)) continue;
    else if (ts.isExpressionStatement(s)) initNodes.push(s);
    // `declare const x: T` runs nothing: the value is assumed at its
    // annotation, like an imported constant's. `declare const k: unique
    // symbol` names a symbol instead, whose declaration is the identity
    // computed keys in types read (the declaration graph's `symbols`); it
    // binds no value, so a read of it as a value is refused where it is read.
    // `declare let` and `declare var` are module storage that outside code
    // may write, which the fragment does not have (as for a module `let`).
    else if (ts.isVariableStatement(s) && ambient(s)) {
      if (!(s.declarationList.flags & ts.NodeFlags.Const))
        gate.fail(s, "a `declare let` or `declare var` is module storage outside the fragment");
      for (const d of s.declarationList.declarations) {
        const type = d.type;
        if (d.initializer || !type || !ts.isIdentifier(d.name))
          return gate.fail(d, "an ambient constant needs a name and an annotation, and no initializer");
        if (!(ts.isTypeOperatorNode(type) && type.operator === ts.SyntaxKind.UniqueKeyword &&
            type.type.kind === ts.SyntaxKind.SymbolKeyword))
          ambientNames.push(d.name);
      }
    }
    else if (ts.isVariableStatement(s)) {
      // A module constant is read by functions at its annotation. Module
      // storage that functions could write is not yet in the fragment.
      if (!(s.declarationList.flags & ts.NodeFlags.Const))
        gate.fail(s, "a module-level `let` or `var` is outside the fragment");
      initNodes.push(s);
    }
    else
      gate.fail(
        s,
        `top-level statement outside the fragment (${ts.SyntaxKind[s.kind]})`,
      );
  }
  // Every module body is strict, including one whose only module syntax is a
  // type-only import. This decides the receiver rule for nested ordinary
  // functions when imported declarations become certifiable.
  gate.strict = prologue.strict || importNodes.length > 0 ||
    interfaceNodes.some(node => node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) ||
    fnNodes.some(fn => fn.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword));
  let declarations: Ast["declarations"] = { roots: [], definitions: [], values: [], symbols: [] };
  const statable = (node: TypeAliasDeclaration): boolean => {
    const params = node.typeParameters;
    return !node.modifiers?.length && params?.length === 1 &&
      !params[0].constraint && !params[0].defaultType;
  };
  const localNodes: Array<TypeAliasDeclaration | InterfaceDeclaration | ClassDeclaration> =
    [...(carriesContext ? aliasNodes.filter(statable) : aliasNodes), ...interfaceNodes, ...classNodes];
  // A type name the file neither imports nor declares may be a global, such
  // as the standard library's `Promise`: TypeScript decides, and a global
  // declaration joins the graph as a root. Each name's first reference
  // stands for it.
  const rooted = new Set<string>([
    ...importNodes.flatMap(node => {
      const bindings = node.importClause?.namedBindings;
      return bindings && ts.isNamedImports(bindings) ? bindings.elements.map(e => e.name.text) : [];
    }),
    ...[...aliasNodes, ...interfaceNodes, ...classNodes, ...enumNodes].flatMap(node => node.name ? [node.name.text] : []),
  ]);
  const globalNodes: Identifier[] = [];
  const findGlobals = (node: Node): void => {
    const typeName = ts.isTypeReferenceNode(node) ? node.typeName : null;
    if (typeName && ts.isIdentifier(typeName) &&
        !rooted.has(typeName.text) && !globalNodes.some(g => g.text === typeName.text))
      globalNodes.push(typeName);
    node.forEachChild(findGlobals);
  };
  if (!carriesContext) findGlobals(source);
  // A value name the file neither imports nor binds may be a global variable,
  // such as Node's `process`: TypeScript decides, and a global variable joins
  // the values, read at the members and call signatures its references
  // select. Every reference
  // in a value position is listed. A computed key names a symbol, which the
  // declaration graph reads itself, and `Object` in `Object.assign` is the
  // intrinsic form above, not a read of the global. A name the file binds
  // anywhere is not listed, so only a file that reads a free name asks
  // TypeScript; a shadowed global stays unbound.
  const bound = new Set<string>(rooted);
  const findBound = (node: Node): void => {
    const name = nameOf(node);
    if ((ts.isParameterDeclaration(node) || ts.isVariableDeclaration(node) || ts.isFunctionDeclaration(node) ||
         ts.isFunctionExpression(node) || ts.isClassDeclaration(node) || ts.isClassExpression(node) ||
         ts.isBindingElement(node) || ts.isEnumDeclaration(node)) && name && ts.isIdentifier(name))
      bound.add(name.text);
    node.forEachChild(findBound);
  };
  findBound(source);
  // A local may shadow a binding of an enclosing scope, as JavaScript's
  // scopes allow. The fragment's scopes are lists of names, so such a local
  // is given a name of its own (`shadowName`), and every reference
  // TypeScript binds to it reads that name.
  const shadowing = shadowingLocals(source);
  const shadowedTexts = new Set([...shadowing.values()].map(d => d.text));
  // Every private name `#x`, a member's and each read, write or call of
  // one: TypeScript binds it to the member declaring it, whose key it is.
  const privateNodes: Node[] = [];
  const findPrivate = (node: Node): void => {
    if (ts.isPrivateIdentifier(node)) privateNodes.push(node);
    node.forEachChild(findPrivate);
  };
  if (!carriesContext) findPrivate(source);
  const bindingNodes: Identifier[] = [];
  // Reads of a shadowing local above its declaration (`bindingRead`).
  const early: Identifier[] = [];
  const findBindingReads = (node: Node): void => {
    if (ts.isTypeNode(node) || ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) return;
    if (ts.isIdentifier(node) && shadowedTexts.has(node.text) &&
        !shadowing.has(`${node.getStart(source)}:${node.end}`))
      bindingNodes.push(node);
    node.forEachChild(findBindingReads);
  };
  for (const [key, id] of shadowing) gate.renames.set(key, shadowName(id, source));
  if (shadowing.size && !carriesContext) findBindingReads(source);
  const globalValueNodes: Identifier[] = [];
  const findGlobalValues = (node: Node): void => {
    if (ts.isTypeNode(node) || ts.isComputedPropertyName(node) || ts.isImportDeclaration(node) ||
        ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node) || ts.isHeritageClause(node))
      return;
    if (ts.isIdentifier(node) && !bound.has(node.text) && node.text !== "undefined") {
      const parent = node.parent;
      const intrinsic = node.text === "Object" && ts.isPropertyAccessExpression(parent) &&
        parent.expression === node && parent.name.text === "assign";
      if (childOf(parent, "name") !== node && childOf(parent, "propertyName") !== node &&
          childOf(parent, "label") !== node && !intrinsic)
        globalValueNodes.push(node);
    }
    node.forEachChild(findGlobalValues);
  };
  if (!carriesContext) findGlobalValues(source);
  // An array reaches `Array.prototype`, whose contract then joins the graph;
  // the first array the file writes stands for it. `Array<T>` is written by
  // name: if TypeScript binds the name elsewhere, the contract is unused.
  let firstArray: Node | undefined;
  const findArray = (node: Node): void => {
    if (firstArray) return;
    const arrayReference = ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) &&
      (node.typeName.text === "Array" || node.typeName.text === "ReadonlyArray");
    if (ts.isArrayTypeNode(node) || ts.isTupleTypeNode(node) || ts.isArrayLiteralExpression(node) || arrayReference ||
        ts.isForOfStatement(node) || (ts.isParameterDeclaration(node) && !!node.dotDotDotToken)) {
      firstArray = node;
      return;
    }
    node.forEachChild(findArray);
  };
  findArray(source);
  // `async`, `await`, `for...of` and `for...in` are calls of intrinsics,
  // which then join the declarations; the first such construct stands for
  // them.
  let firstAsync: Node | undefined;
  const intrinsicNames = new Set<string>();
  const findAsync = (node: Node): void => {
    const add = (...names: string[]) => {
      firstAsync ??= node;
      names.forEach(name => intrinsicNames.add(name));
    };
    if (ts.isAwaitExpression(node)) add(awaitName);
    if (ts.isForOfStatement(node)) add(iterateName);
    if (ts.isForInStatement(node))
      add(...(forInEntryReads(node).length ? [iterateForInName] : [forInName, iterateName]));
    if (ts.isFunctionLikeDeclaration(node) &&
        node.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword))
      add(asyncReturnName, asyncCompleteName);
    node.forEachChild(findAsync);
  };
  if (!carriesContext) findAsync(source);
  // The keys of `k in o` tests: TypeScript's type of each decides whether
  // the test is the model's key test or the host's `%HasProperty%`.
  const inKeyNodes: Node[] = [];
  const findInKeys = (node: Node): void => {
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.InKeyword) {
      const key = inKey(node);
      if (!ts.isPrivateIdentifier(key)) inKeyNodes.push(key);
    }
    node.forEachChild(findInKeys);
  };
  if (!carriesContext) findInKeys(source);
  // The member names of `o.m.call(…)`, `.apply` and `.bind`: TypeScript
  // decides which is a method, whose receiver is its host.
  const receiverTargetNodes: Node[] = [];
  const findReceiverTargets = (node: Node): void => {
    if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
        ["call", "apply", "bind"].includes(node.expression.name.text)) {
      let target: Expression = node.expression.expression;
      while (ts.isParenthesizedExpression(target)) target = target.expression;
      if (ts.isPropertyAccessExpression(target) && ts.isIdentifier(target.name)) receiverTargetNodes.push(target.name);
    }
    node.forEachChild(findReceiverTargets);
  };
  if (!carriesContext) findReceiverTargets(source);
  // Element reads `e[k]` other than a write's target: TypeScript's types of
  // the object and the key decide whether `%ElementAt%` reads it.
  const elementReadNodes: Node[] = [];
  const findElementReads = (node: Node): void => {
    if (ts.isElementAccessExpression(node) && !node.questionDotToken && !writtenElement(node))
      elementReadNodes.push(node);
    node.forEachChild(findElementReads);
  };
  if (!carriesContext) findElementReads(source);
  // An identifier as an element key, `e[k]`, may name a `unique symbol`
  // constant, and `e[S.k]` a `unique symbol` property, such as the
  // well-known `Symbol.iterator`: TypeScript decides, and such a key joins
  // the symbols.
  const keyNodes: Node[] = [];
  const findKeys = (node: Node): void => {
    if (ts.isElementAccessExpression(node) && (ts.isIdentifier(node.argumentExpression) ||
        (ts.isPropertyAccessExpression(node.argumentExpression) && ts.isIdentifier(node.argumentExpression.expression) &&
          ts.isIdentifier(node.argumentExpression.name))))
      keyNodes.push(node.argumentExpression);
    // A static method's computed key, `static [Symbol.hasInstance]`.
    if (ts.isComputedPropertyName(node) && node.parent && ts.isMethodDeclaration(node.parent) &&
        node.parent.modifiers?.some((m) => m.kind === ts.SyntaxKind.StaticKeyword) &&
        ts.isPropertyAccessExpression(node.expression) && ts.isIdentifier(node.expression.expression) &&
        ts.isIdentifier(node.expression.name))
      keyNodes.push(node.expression);
    node.forEachChild(findKeys);
  };
  if (!carriesContext) findKeys(source);
  // A member read of a primitive, `s.length` or `n.toString()`, reads through
  // its wrapper's prototype: TypeScript's type of the receiver decides.
  const receiverNodes: Node[] = [];
  const findReceivers = (node: Node): void => {
    if (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node))
      receiverNodes.push(node.expression);
    node.forEachChild(findReceivers);
  };
  if (!carriesContext) findReceivers(source);
  // A `for...of` loop steps the iteration intrinsic of its iterable's kind:
  // TypeScript's type of the iterable decides.
  const iterableNodes: Node[] = [];
  // An argument spread likewise collects its operand's elements.
  const spreadNodes: Node[] = [];
  // So do an array literal's spreads and an array pattern's initializer,
  // which step the iterator of a program's iterable (`protocolForOf`).
  const findIterables = (node: Node): void => {
    if (ts.isForOfStatement(node)) iterableNodes.push(node.expression);
    if (ts.isCallExpression(node) || ts.isArrayLiteralExpression(node))
      for (const arg of ts.isCallExpression(node) ? node.arguments : node.elements)
        if (ts.isSpreadElement(arg)) spreadNodes.push(arg.expression);
    if (ts.isVariableDeclaration(node) && ts.isArrayBindingPattern(node.name) && node.initializer)
      iterableNodes.push(node.initializer);
    node.forEachChild(findIterables);
  };
  if (!carriesContext) findIterables(source);
  // An array pattern's rest is a slice where TypeScript types its target as
  // no one tuple of required positions: TypeScript's type decides.
  const restTargets: { node: Node; index: number }[] = [];
  const findRests = (node: Node): void => {
    // The source a rest slices: the pattern's own value, or an assignment's
    // right side.
    if (ts.isArrayBindingPattern(node))
      node.elements.forEach((el, index) => {
        if (ts.isBindingElement(el) && el.dotDotDotToken) restTargets.push({ node, index });
      });
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
        ts.isArrayLiteralExpression(node.left))
      node.left.elements.forEach((el, index) => {
        if (ts.isSpreadElement(el)) restTargets.push({ node: node.right, index });
      });
    node.forEachChild(findRests);
  };
  if (!carriesContext) findRests(source);
  // A read `C.x` of a class with static members may be one of them:
  // TypeScript decides.
  const withStatics = new Set(classNodes.filter(c => c.members.some(isStatic))
    .flatMap(c => c.name ? [c.name.text] : []));
  const staticNodes: Identifier[] = [];
  const findStatics = (node: Node): void => {
    if (ts.isPropertyAccessExpression(node) && ts.isIdentifier(node.expression) &&
        withStatics.has(node.expression.text) && ts.isIdentifier(node.name))
      staticNodes.push(node.name);
    node.forEachChild(findStatics);
  };
  if (!carriesContext && withStatics.size) findStatics(source);
  // `x instanceof C` of a class the file declares: TypeScript decides which
  // right operands name it.
  const classNames = new Set(classNodes.flatMap(c => c.name ? [c.name.text] : []));
  const classTestNodes: Identifier[] = [];
  const findClassTests = (node: Node): void => {
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword &&
        ts.isIdentifier(node.right) && classNames.has(node.right.text))
      classTestNodes.push(node.right);
    node.forEachChild(findClassTests);
  };
  if (!carriesContext && classNames.size) findClassTests(source);
  // `x instanceof c` of another name: TypeScript decides whether the type of
  // `c` states `[Symbol.hasInstance]`.
  const hookTestNodes: Identifier[] = [];
  const findHookTests = (node: Node): void => {
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword &&
        ts.isIdentifier(node.right) && !classNames.has(node.right.text))
      hookTestNodes.push(node.right);
    node.forEachChild(findHookTests);
  };
  if (!carriesContext) findHookTests(source);
  // A class's own name in its body: TypeScript decides which name it.
  const classReadNodes: Identifier[] = [];
  for (const c of classNodes) {
    const own = c.name?.text;
    const findReads = (node: Node): void => {
      if (ts.isTypeNode(node)) return;
      if (ts.isIdentifier(node) && node.text === own) classReadNodes.push(node);
      node.forEachChild(findReads);
    };
    if (!carriesContext && own) c.members.forEach(findReads);
  }
  const classTestKeys = new Set(classTestNodes.map(node => gate.span(node).join(":")));
  const classReadKeys = new Set(classReadNodes.map(node => gate.span(node).join(":")));
  // A closure parameter without a type: TypeScript gives it one from its
  // context.
  // A static field written without an annotation: TypeScript gives it a
  // type, which the class value's type states.
  const staticTypeNodes: Node[] = [];
  for (const c of classNodes)
    for (const m of c.members)
      if (ts.isPropertyDeclaration(m) && !m.type && ts.isIdentifier(m.name) &&
          m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword))
        staticTypeNodes.push(m.name);
  const contextualNodes: Node[] = [];
  const findContextual = (node: Node): void => {
    if (ts.isParameterDeclaration(node) && !node.type && !node.dotDotDotToken && node.parent &&
        (ts.isArrowFunction(node.parent) || ts.isFunctionExpression(node.parent) ||
          (ts.isMethodDeclaration(node.parent) && ts.isObjectLiteralExpression(node.parent.parent))))
      contextualNodes.push(node.name);
    node.forEachChild(findContextual);
  };
  if (!carriesContext) findContextual(source);
  // `Object.assign(arrow, literal)` without type arguments is the callable
  // form at the two TypeScript infers.
  const assignNodes: Node[] = [];
  const findAssign = (node: Node): void => {
    if (callableAssign(node) && !node.typeArguments) assignNodes.push(node);
    node.forEachChild(findAssign);
  };
  if (!carriesContext) findAssign(source);
  // A read `X.y` or `X["y"]` of a `const enum` is its member's value:
  // TypeScript decides which reads are.
  const inlined = new Set(enumNodes.filter(e => e.modifiers?.some(m => m.kind === ts.SyntaxKind.ConstKeyword))
    .map(e => e.name.text));
  const constEnumNodes: Node[] = [];
  const findConstEnumReads = (node: Node): void => {
    if ((ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node)) &&
        ts.isIdentifier(node.expression) && inlined.has(node.expression.text))
      constEnumNodes.push(node);
    node.forEachChild(findConstEnumReads);
  };
  if (inlined.size) findConstEnumReads(source);
  // A type TypeScript computes from others, `typeof x`, `keyof T`, `T[K]` or
  // a template literal type, is the type its evaluation denotes: each
  // outermost one in an annotation is evaluated where it is written. Those
  // in type declarations are the declaration graph's own.
  // A computed key of a type literal, `{ [k]: T }`, names a symbol:
  // TypeScript decides which.
  const computedNodes: Node[] = [];
  const symbolNameNodes: Node[] = [];
  const keyTypeNodes: Node[] = [];
  // The file's aliases TypeScript computes from their parameters
  // (`computedAlias`): an application of one is a computed type too.
  const localAlias = (reference: ts.TypeReferenceNode): TypeAliasDeclaration | null => {
    const typeName = reference.typeName;
    return ts.isIdentifier(typeName) ? aliasNodes.find(a => a.name.text === typeName.text) ?? null : null;
  };
  const computedAliases = new Set(aliasNodes.filter(a => computedAlias(a, localAlias)).map(a => a.name.text));
  const findComputed = (node: Node): void => {
    if (ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)) return;
    if (ts.isTypeNode(node) && (computedForm(node) !== null ||
        (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && computedAliases.has(node.typeName.text) &&
          !enclosingBinders(node).includes(node.typeName.text)))) {
      computedNodes.push(node);
      return;
    }
    // So does the computed key of a class method or an object literal's
    // property or method, `[Symbol.iterator]() { … }`.
    if (ts.isComputedPropertyName(node) && node.parent &&
        (ts.isPropertySignatureDeclaration(node.parent) || ts.isMethodSignatureDeclaration(node.parent) ||
          ts.isMethodDeclaration(node.parent) || ts.isPropertyAssignment(node.parent)))
      symbolNameNodes.push(node.expression);
    // A mapped type's keys, and a global generic's arguments, which may be
    // a library mapped type's keys, `Record<K, V>`: TypeScript computes them.
    if (ts.isMappedTypeNode(node) && node.typeParameter.constraint) keyTypeNodes.push(node.typeParameter.constraint);
    if (ts.isIndexSignatureDeclaration(node) && node.parameters[0]?.type) keyTypeNodes.push(node.parameters[0].type);
    if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && !rooted.has(node.typeName.text))
      keyTypeNodes.push(...(node.typeArguments ?? []));
    node.forEachChild(findComputed);
  };
  if (!carriesContext) findComputed(source);
  if (importNodes.length || localNodes.length || globalNodes.length || globalValueNodes.length ||
      firstArray || firstAsync || keyNodes.length || ambientNames.length || staticNodes.length ||
      classTestNodes.length || classReadNodes.length || contextualNodes.length || assignNodes.length ||
      staticTypeNodes.length ||
      hookTestNodes.length || receiverNodes.length || enumNodes.length || computedNodes.length || symbolNameNodes.length ||
      keyTypeNodes.length || bindingNodes.length || iterableNodes.length || spreadNodes.length ||
      restTargets.length || privateNodes.length || inKeyNodes.length || receiverTargetNodes.length || elementReadNodes.length) {
    const first = importNodes[0] ?? localNodes[0] ?? globalNodes[0] ?? globalValueNodes[0] ?? firstArray ??
      firstAsync ?? keyNodes[0] ?? ambientNames[0] ?? staticNodes[0] ?? classTestNodes[0] ?? classReadNodes[0] ?? contextualNodes[0] ?? assignNodes[0] ??
      hookTestNodes[0] ?? staticTypeNodes[0] ?? receiverNodes[0] ?? enumNodes[0] ??
      computedNodes[0] ?? symbolNameNodes[0] ?? keyTypeNodes[0] ?? bindingNodes[0] ?? iterableNodes[0] ??
      spreadNodes[0] ?? restTargets[0]?.node ?? privateNodes[0] ?? inKeyNodes[0] ?? receiverTargetNodes[0] ?? elementReadNodes[0];
    if (!first) throw Error("missing declaration root");
    // Named imports only. A type import joins the declaration graph; a value
    // import is an assumption at the type its declaration states.
    for (const node of importNodes) {
      const clause = node.importClause;
      if (!clause || clause.name || !clause.namedBindings ||
          !ts.isNamedImports(clause.namedBindings))
        gate.fail(node, "only named imports are in the source fragment");
    }
    // TypeScript resolves every name, in the project that owns the file or the
    // one named explicitly: the declaration graph is the compiler's.
    try {
      declarations = collectDeclarations(resolutionFile, { tsconfigPath, client: source,
        locals: localNodes.map(node => gate.span(node)),
        globals: globalNodes.map(node => gate.span(node)),
        globalValues: globalValueNodes.map(node => gate.span(node)),
        ambient: ambientNames.map(node => gate.span(node)),
        ...(firstArray ? { arrays: gate.span(firstArray) } : {}),
        ...(firstAsync ? { intrinsics: { span: gate.span(firstAsync), names: [...intrinsicNames] } } : {}),
        symbolKeys: keyNodes.map(node => gate.span(node)),
        symbolKey: ([start, end], symbol) => gate.symbolKeys.set(`${start}:${end}`, symbol),
        staticReads: staticNodes.map(node => gate.span(node)),
        staticMember: ([start, end], cls) => gate.staticReads.set(`${start}:${end}`, cls),
        inheritedStatic: ([start, end]) => gate.inheritedStatics.add(`${start}:${end}`),
        classTests: [...classTestNodes, ...classReadNodes].map(node => gate.span(node)),
        classTest: ([start, end], cls) => {
          const key = `${start}:${end}`;
          if (classTestKeys.has(key)) gate.classTests.set(key, cls);
          if (classReadKeys.has(key)) gate.classReads.set(key, cls);
        },
        hookTests: hookTestNodes.map(node => gate.span(node)),
        hookTest: ([start, end]) => gate.hookTests.add(`${start}:${end}`),
        privateNames: privateNodes.map(node => gate.span(node)),
        privateName: ([start, end], symbol) => gate.privateKeys.set(`${start}:${end}`, symbol),
        bindingReads: bindingNodes.map(node => gate.span(node)),
        bindingRead: ([start, end], [dStart, dEnd]) => {
          const declared = shadowing.get(`${dStart}:${dEnd}`);
          const renamed = gate.renames.get(`${dStart}:${dEnd}`);
          if (!declared || renamed === undefined) return;
          // JavaScript gives a block's declared name to the declaration from
          // the block's start: a mention above the declaration, a closure's
          // included, or in its own initializer is its binding before it is
          // initialized (the temporal dead zone), never the outer one. A
          // pattern's element may name one bound before it in the pattern.
          const read = bindingNodes.find(n => n.getStart(source) === start && n.end === end);
          let declaration: Node | undefined = declared.parent;
          while (declaration && ts.isBindingElement(declaration)) declaration = declaration.parent?.parent;
          const initializer = declaration && ts.isVariableDeclaration(declaration) ? declaration.initializer : undefined;
          const inInitializer = !!initializer && start >= initializer.getStart(source) && end <= initializer.end;
          if (read && (start < dStart || inInitializer)) early.push(read);
          gate.renames.set(`${start}:${end}`, renamed);
        },
        staticTypes: staticTypeNodes.map(node => gate.span(node)),
        staticType: ([start, end], result) => gate.staticTypes.set(`${start}:${end}`, result),
        contextualParams: contextualNodes.map(node => gate.span(node)),
        contextualParam: ([start, end], result) => gate.contextualParams.set(`${start}:${end}`, result),
        assignCalls: assignNodes.map(node => gate.span(node)),
        assignTypes: ([start, end], result) => gate.assignTypes.set(`${start}:${end}`, result),
        memberReceivers: receiverNodes.map(node => gate.span(node)),
        iterables: iterableNodes.map(node => gate.span(node)),
        spreads: spreadNodes.map(node => gate.span(node)),
        iterable: ([start, end], intrinsic, symbol) => {
          gate.iterations.set(`${start}:${end}`, intrinsic);
          if (symbol !== null) gate.wellKnownIterator = symbol;
        },
        inKeys: inKeyNodes.map(node => gate.span(node)),
        hostIn: ([start, end]) => gate.hostIns.add(`${start}:${end}`),
        receiverTargets: receiverTargetNodes.map(node => gate.span(node)),
        methodTarget: ([start, end]) => gate.methodTargets.add(`${start}:${end}`),
        elementReads: elementReadNodes.map(node => gate.span(node)),
        hostElement: ([start, end]) => gate.hostElements.add(`${start}:${end}`),
        restTargets: restTargets.map(({ node, index }) => ({ span: gate.span(node), index })),
        restSlice: ([start, end]) => gate.slices.add(`${start}:${end}`),
        computed: computedNodes.map(node => gate.span(node)),
        computedType: ([start, end], result) => gate.computedTypes.set(`${start}:${end}`, result),
        symbolNames: symbolNameNodes.map(node => gate.span(node)),
        keyTypes: keyTypeNodes.map(node => gate.span(node)),
        keyType: ([start, end], keys) => gate.keyTypes.set(`${start}:${end}`, keys),
        symbolName: ([start, end], result) => gate.symbolNames.set(`${start}:${end}`, result),
        globalTest: ([start, end]) => gate.globalTests.add(`${start}:${end}`),
        globalIntrinsic: ([start, end], name) => gate.globalIntrinsics.set(`${start}:${end}`, name),
        enums: enumNodes.map(node => gate.span(node)),
        enumMember: ([start, end], value) => {
          for (const info of gate.enums.values())
            for (const m of info.members) if (m.span[0] === start && m.span[1] === end) m.value = value;
        },
        enumMemberRead: ([start, end], member) => gate.enumMemberReads.set(`${start}:${end}`, member.join(":")),
        constEnumReads: constEnumNodes.map(node => gate.span(node)),
        constEnumRead: ([start, end], value) => gate.constEnumReads.set(`${start}:${end}`, value),
        library: ([start, end], library) => {
          const node = globalNodes.find(n => n.getStart(source) === start && n.end === end);
          if (node) gate.libraryTypes.set(node.text, library);
        },
        awaited: () => { gate.standardAwaited = true; },
        resolvable: () => { gate.standardResolvable = true; },
        awaitable: () => { gate.standardAwaitable = true; },
        associatedAlias: (name, identity) => {
          const alias = aliasNodes.find(node => node.name.text === name &&
            node.getStart(source) === identity.span[0] && node.end === identity.span[1]);
          if (alias) gate.resolutionAliases.set(name, alias);
          else gate.fail(null, "an external associated-result alias requires retained symbol resolution");
        },
        ...(seen ? { seen } : {}) });
      gate.symbolIdentities = declarations.symbols;
    } catch (error) {
      const at = error instanceof DeclarationError
        ? [...importNodes, ...localNodes, ...globalNodes, ...globalValueNodes, ...(firstArray ? [firstArray] : []),
            ...(firstAsync ? [firstAsync] : []), ...keyNodes, ...ambientNames.map(topStatement), ...staticNodes,
            ...classTestNodes, ...classReadNodes, ...contextualNodes, ...assignNodes,
            ...receiverNodes, ...enumNodes, ...constEnumNodes, ...computedNodes, ...symbolNameNodes,
            ...keyTypeNodes, ...bindingNodes, ...privateNodes].find(node =>
            node.getStart(source) === error.at[0]) ?? first
        : first;
      gate.fail(at, messageOf(error));
    }
    if (early[0])
      gate.fail(early[0], `a read of \`${early[0].text}\` before its declaration: JavaScript throws there (the temporal dead zone)`);
    // The standard library's well-known symbols the host reads off the
    // objects a literal or a class's prototype makes: all but
    // `Symbol.iterator`, whose protocol the model runs, and
    // `Symbol.hasInstance`, which only `instanceof` reads, off its right
    // operand (`binary`), and calls where that operand's type states it.
    gate.hostSymbols = new Set(declarations.symbols.flatMap((s, i) =>
      s.module.startsWith("typescript/lib/") && s.name !== "iterator" && s.name !== "hasInstance" ? [i] : []));
    for (const { declaration } of declarations.definitions)
      gate.typeIdentities.add(JSON.stringify([declaration.module, declaration.span, declaration.name]));
    for (const root of declarations.roots) {
      const identity = root.declaration;
      const definition = declarations.definitions.find(d =>
        d.declaration.module === identity.module && d.declaration.name === identity.name &&
        d.declaration.span[0] === identity.span[0] &&
        d.declaration.span[1] === identity.span[1]);
      if (!definition)
        return gate.fail(first, `type definition missing: ${identity.module}#${identity.name}`);
      const node = [...importNodes, ...localNodes, ...globalNodes].find(n =>
        n.getStart(source) === root.binding.span[0]) ?? first;
      gate.registerDeclaredType(root.binding.local,
        definition.parameters.filter(p => p.default === null).length,
        definition.parameters.length, identity, node, definition.expression);
    }
  }
  // Carried context skips aliases its old fragment could not state. Every
  // retained declaration now has one source equation, shared with imports.
  // A function without a body is a declaration, not an example of one.
  const declared = carriesContext ? fnNodes.filter((s) => s.body) : fnNodes;
  const functions = declared.map((s) => gate.functionDecl(s));
  // Every enum's members must have values, whether or not it runs.
  for (const e of enumNodes) gate.enumMembers(e.name.text);
  const init = initNodes.flatMap((s) => ts.isClassDeclaration(s) ? [gate.classStmt(s)]
    : ts.isEnumDeclaration(s) ? gate.enumStmt(s) : [gate.stmt(s)]);
  if (functions.length === 0 && init.length === 0) gate.fail(null, "no functions in file");
  return {
    file,
    sourceSha256: createHash("sha256").update(text).digest("hex"),
    declarations,
    functions,
    init,
  };
}


/* ---------------------------------------------------------------- main -- */

// Run as a command, or lend the type translation to another trusted tool. The
// annotation encoding must have exactly one implementation: a second one would
// be a second opinion about what a source type means.
if (process.argv[1] && import.meta.filename === resolve(process.argv[1])) {
  const [file, ...rest] = process.argv.slice(2);
  const options = new Map<string, string>();
  for (let [flag, value] = rest; flag !== undefined && value !== undefined &&
      ["--project", "--typescript-diagnostics"].includes(flag) && !options.has(flag); [flag, value] = rest) {
    options.set(flag, value);
    rest.splice(0, 2);
  }
  if (!file || rest.length) {
    process.stderr.write("usage: fragment-parse.mts <file.ts> [--project tsconfig-or-directory]" +
      " [--typescript-diagnostics out.json]\n");
    process.exit(2);
  }
  // The TypeScript errors the gate read, written whether or not it accepts
  // the source: a refusal over one of them is located by them.
  const seen: SeenDiagnostic[] = [];
  const project = options.get("--project");
  try {
    process.stdout.write(JSON.stringify(parseFile(file, false,
      project ? tsconfigOf(project) : undefined, file, (d) => seen.push(d)), null, 1));
    close();
  } catch (error) {
    process.stderr.write(messageOf(error) + "\n");
    process.exitCode = 1;
  } finally {
    const out = options.get("--typescript-diagnostics");
    if (out) writeFileSync(out, JSON.stringify(seen, null, 1) + "\n");
  }
}
