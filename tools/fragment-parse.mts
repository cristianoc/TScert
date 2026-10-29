#!/usr/bin/env node
import { recoverGate, refusal, refusalOf, type GateOccurrence } from "./diagnostic-gate.mts";
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
 * never sees the producer's own parse. The gate's methods for enums and classes,
 * expressions, and patterns and statements are in fragment-classes.mts,
 * fragment-expressions.mts and fragment-statements.mts; the helpers they share
 * are in fragment-support.mts. All five are this one trusted program. The fragment it accepts is stated in
 * ../AGENTS.md and, as a grammar, in the pull request description.
 */
import { type API, SymbolFlags, type Checker, type Project } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, Expression, FunctionDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, ParameterDeclaration, SourceFile, Statement, TypeAliasDeclaration, TypeParameterDeclaration, VariableStatement, TypeNode } from "typescript/unstable/ast";
import { createHash } from "node:crypto";
// files.mts makes every file-system failure a tool failure.
import { noteInput, readText, writeText } from "./files.mts";
import { dirname, resolve } from "node:path";
import type { DeclarationIdentity, ResolutionSlots, StatedEffect, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { deepPartMap, mapDocument, mapFunctionParts } from "./fragment-parts.mts";
import { computedAlias, computedForm, optionalTerm, resolutionSlots, restPositions, restRefusal, restTerm, REST_PACK_BOUND, REST_PACK_VALUE, statedResult, substitute, typeTerm, visitType, mapTypeParts, type MappedMember, type TermScope } from "./type-term.mts";
import type { Ast, Expr, ModuleAst, Stmt, TypeParamAst } from "./fragment.mts";
import type { Span } from "./span.mts";
import { requireWellFormedText, wellFormedTextRefusal } from "./wire-strings.mts";
// thrown.mts reads what the TypeScript API throws into the message the gate reports, without asserting its type.
import { messageOf, passToolFailure, toolFailureOf, toolFailureText, type ToolFailure } from "./thrown.mts";
// syntax.mts reads the name, modifiers and other children a member or declaration of unasked kind carries, checking each is a node.
import { childOf, isStatic, nameOf, isTypeAlias } from "./syntax.mts";
import { enclosingBinders } from "./computed-types.mts";
// named-record.mts reads a named type's record shape, which a mapped type over it maps.
import { definitionKey, deferredInAst, deferredInModule, recordShape, settleTerm, type NamedRecords } from "./named-record.mts";
// declaration-graph.mts collects the declarations the source reaches: the declaration document the Fragment carries for Lean to lower.
import { collectDeclarations, expressionAt, libraryArguments, libraryTerm, declarationSpanOf, tsconfigOf, type Answered,
  type BlockType, type LibraryType, type SeenDiagnostic }
  from "./declaration-graph.mts";
// compiler-channel.mts opens and releases the compiler, every request's failure a tool failure.
import { openFrontEndCompiler, releaseCompiler } from "./compiler-channel.mts";
import { asyncCompleteName, asyncReturnName, awaitName, enumMembersTerm, forInName, iterateForInName, iterateName, literalTerm,
  throwUninitializedName, objectProtoKeys, type EnumMemberValue, type EnumReverse } from "./intrinsics.mts";
import { isDispatchMethod } from "./regexp.mts";
import type { GuardUndefined, TagValue } from "./host-families.mts";
import { type ClassRecord, type EnumInfo, type EnumMember, SPREAD_POSITION, isTagSymbol, callableAssign, forInEntryReads, inKey, readOf, shadowName, shadowingLocals, typeParameterMentioned, writesName, writtenElement, callTarget } from "./fragment-support.mts";
import * as classes from "./fragment-classes.mts";
import * as expressions from "./fragment-expressions.mts";
import * as statements from "./fragment-statements.mts";
import * as guards from "./fragment-guards.mts";
import { memberUses, namespaceMembers, type MemberUse, type NamespaceMember } from "./namespace-members.mts";

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
/** How many compilers the parser opened in this process, for the controls:
 * each parse opens its own. */
let openings: number = 0;
export const parserOpenings = (): number => openings;

/**
 * The project that owns a file: whichever `tsconfig.json` above it claims it,
 * or an inferred one. Exported because a checker-side consumer of this parse
 * needs the same project (and the same compiler process) the gate used.
 */
function projectFor(absolute: string): Project {
  if (!compiler) {
    compiler = openFrontEndCompiler(dirname(absolute), contents);
    openings++;
  }
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

function openFile(absolute: string, text: string): { file: SourceFile; checker: Checker } {
  contents.set(absolute, text);
  const project = projectFor(absolute);
  const syntax = project.program.getSyntacticDiagnostics(absolute);
  if (syntax.length > 0)
    throw new Error(`gate: parse error: ${syntax[0].text}`);
  const file = project.program.getSourceFile(absolute);
  if (!file)
    throw new Error(`gate: the compiler produced no tree for ${absolute}`);
  return { file, checker: project.checker };
}

/** Release the compiler. A long-lived caller may parse again afterwards. */
export function close(): void {
  release(null);
}

/** The parser's state reset, then its compiler released as
 * `releaseCompiler` does after `thrown`: the next parse opens another,
 * whatever releasing this one does. */
function release(thrown: { error: unknown } | null): void {
  const held = compiler;
  compiler = null;
  opened.clear();
  contents.clear();
  if (held) releaseCompiler(held, thrown);
}

/* -------------------------------------------------------------- the gate -- */
// One parse owns one source file. `fail` and `span` are the only two things
// that need it, and they are the only two that should: a gate rejection names
// a place in the file it is reading.

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators, bigint) is outside it.

export class Gate {
  // Written out rather than a parameter property: node strips types, it does
  // not compile them, so the syntax has to be erasable.
  readonly file: SourceFile;
  /* Type-parameter names are resolved lexically. Keeping frames, rather than
   * one file-wide set, makes nested quantified callables representable without
   * conflating an inner binder with an outer binder of the same spelling.
   * Leaving a frame replaces each stack by its remainder, a field write, and
   * no reader keeps either stack (SOURCE-REWRITES.md, "A stack popped
   * through a field"). */
  typeParamScopes: Map<string, string>[] = [];
  resolutionScopes: TypeParamAst[][] = [];
  readonly resolutionAliases: Map<string, TypeAliasDeclaration> = new Map();
  standardAwaited: boolean = false;
  /** The file names the verifier's `Resolvable` (`resolvable.d.ts`). */
  standardResolvable: boolean = false;
  /** The file names the verifier's `Awaitable` (`resolvable.d.ts`). */
  standardAwaitable: boolean = false;
  /** The file names the verifier's `Within` (`resolvable.d.ts`), a
   * signature's statement of its effect. */
  standardWithin: boolean = false;
  qualificationHeader: boolean = false;
  /** Local spelling to the arity and identity of its declaration root. A
   * reference names the declaration TypeScript resolved the spelling to. */
  /** The equations of the declared aliases that name an array, a tuple or
   * another alias, over their parameters: what a rest parameter typed by one
   * collects into (`restType`, `restTerm`), by identity (`identityKey`):
   * a module root's and a type declared in a block's, whose parameters
   * start with those it closes over. */
  readonly aliasEquations: Map<string, { total: number; expression: TypeTerm }> = new Map();
  readonly declaredTypes: Map<string,
    { required: number; total: number; declaration: DeclarationIdentity }> = new Map();
  /** Global spellings TypeScript binds to a standard library type read at
   * its meaning, `Array<T>` as `T[]` (`LibraryType`). */
  readonly libraryTypes: Map<string, LibraryType> = new Map();
  /** The declaration document's definitions by identity (`definitionKey`),
   * once it is complete, and those that are records written as one: a
   * named type's record shape is read from them (`recordShape`). */
  recordDefinitions: ReadonlyMap<string, TypeDefinition> | null = null;
  readonly recordKeys: Set<string> = new Set();
  /* Whether the code being read is strict, by a module or a "use strict"
   * directive (ECMAScript's, not TypeScript's `strict` option). An ordinary
   * function records it: its receiver rule is the strict one. */
  strict: boolean = false;
  /** `e[k]` keys TypeScript binds to a `unique symbol` constant, by span:
   * the symbol, as the declaration document lists it. */
  symbolKeys: Map<string, number> = new Map();
  /** The symbols the declaration document lists, by index: which one a
   * computed class member's key names. */
  symbolIdentities: readonly { module: string; name: string }[] = [];
  /** Private names `#x`, by span: the symbol of the member each names, as
   * the declaration document lists it. */
  readonly privateKeys: Map<string, number> = new Map();
  /** The computed types of the file's annotations (`computedForm`), by span:
   * the term TypeScript's evaluation denotes, or the reason it has none
   * (`computed-types.mts`). */
  readonly computedTypes: Map<string, Answered<TypeTerm>> = new Map();
  /** The omitted arguments of the file's references to declarations, by
   * span: each the parameter's default at the arguments before it, or the
   * reason it has none. */
  readonly completions: Map<string, Answered<TypeTerm[]>> = new Map();
  /** The file's type references TypeScript binds to a type declared in one
   * of its blocks, by span: that declaration, or the reason it is refused
   * (`blockTypes` of the declaration graph). */
  readonly blockTypes: Map<string, Answered<BlockType>> = new Map();
  /** The computed keys of the file's annotations' type literals, by span of
   * the key expression: the `unique symbol` each names, as the declaration
   * document lists it, or the reason it names none. */
  readonly symbolNames: Map<string, Answered<number | { literal: string; value: string | number }>> = new Map();
  /** Mapped types' keys and library mapped types' arguments in the file's
   * annotations, by span: the union of literals and primitives TypeScript
   * computes for each, or null. */
  readonly keyTypes: Map<string, TypeTerm | null> = new Map();
  /** Mapped types over `keyof` in the file's annotations, by span: their
   * members as TypeScript resolves them, or null. */
  readonly mappedMembers: Map<string, readonly MappedMember[] | null> = new Map();
  /** `C.x` member names TypeScript binds to a static member of the file's
   * class `C`, by span: the class. */
  staticReads: Map<string, string> = new Map();
  /** `X.m` reads of a static member a base class of `X` declares
   * (`inheritedStatic`), by span. */
  readonly inheritedStatics: Set<string> = new Set();
  /** `instanceof` right operands TypeScript binds to a class declared at the
   * file's top level, by span: the class. */
  readonly classTests: Map<string, string> = new Map();
  /** `instanceof` right operands whose type TypeScript gives states
   * `[Symbol.hasInstance]`, by span. */
  readonly hookTests: Set<string> = new Set();
  /** `instanceof` right operands TypeScript binds to an import of a class
   * declaration another module of the program checks, whose type states no
   * `[Symbol.hasInstance]` (`importedClassTest`), by span. */
  readonly importedClassTests: Set<string> = new Set();
  /** A `for...of` iterable's iteration intrinsic, where TypeScript's type of
   * it picks one other than `%Iterate%`, or, for a program's iterable,
   * `client`, `client-method` (its iterator's `return` a required method) or
   * `client-unclosable` (its iterator's type states no `return`), by the
   * iterable's span; likewise a spread's operand and an array pattern's
   * initializer. */
  readonly iterations: Map<string, string> = new Map();
  /** The keys of `k in o` tests the host answers (`%HasProperty%`). */
  readonly hostIns: Set<string> = new Set();
  /** The member names of `o.m.call(…)`, `.apply` and `.bind` TypeScript
   * resolves to a method. */
  readonly methodTargets: Set<string> = new Set();
  /** The element reads `%ElementAt%` answers. */
  readonly hostElements: Set<string> = new Set();
  /** The element reads at a number and the `length` reads of a view of
   * bytes, by span: the intrinsic reading each (`library-types.mts`). */
  readonly byteReads: Map<string, string> = new Map();
  /** The open reads `%Read:k%` answers, by span: each its intrinsic. */
  readonly openReads: Map<string, string> = new Map();
  /** Each regular expression literal's intrinsic, `%RegExp:Σ%`, by span. */
  readonly regexps: Map<string, string> = new Map();
  /** Each string method call dispatching to its object argument's
   * well-known-symbol method, by the call's span: `%Dispatch:m%`. */
  readonly dispatches: Map<string, string> = new Map();
  /** The reads `for...in` bodies start with at their keys
   * (`forInEntryReads`), by span: the hidden name of the entry the loop's
   * step yields. */
  readonly entryReads: Map<string, string> = new Map();
  /** The well-known `Symbol.iterator`'s index among the declaration
   * document's symbols, where a program iterable is iterated. */
  wellKnownIterator: number | null = null;
  /** The standard library's well-known symbols the host reads off an
   * object a literal or a class's prototype makes (`Symbol.toStringTag`,
   * `Symbol.toPrimitive`, …), by index: keys no literal or class of the
   * fragment writes (`writtenSymbol`). */
  hostSymbols: Set<number> = new Set();
  /** The declaration document's entries for the standard library's
   * `Symbol.toStringTag`, by index. */
  tagSymbols: Set<number> = new Set();
  /** The statement being lowered, where it runs a program iterable's
   * protocol before its own code (`hoistTarget`): the spread collected, and
   * the claim sites the lowering takes from the statement. */
  hoist: { stmt: Statement; spread: ts.SpreadElement | null;
    site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> } } | null = null;
  /** The statements a lowering runs before the statement being lowered. */
  hoisted: Stmt[] = [];
  /** The array pattern rest targets TypeScript types as a slice, by span. */
  readonly slices: Set<string> = new Set();
  /** Identifiers in a class's own body TypeScript binds to that class, by
   * span: the class. */
  readonly classReads: Map<string, string> = new Map();
  /** Identities of the declarations collected in the source type graph. */
  readonly typeIdentities: Set<string> = new Set();
  /** Closure parameters written without a type, by the span of their name:
   * the type TypeScript gives each from its context, or why none states it. */
  readonly contextualParams: Map<string, Answered<TypeTerm>> = new Map();
  /** The type TypeScript gives each static field written without an
   * annotation, by its name's span, or why none. */
  readonly staticTypes: Map<string, Answered<TypeTerm>> = new Map();
  /** The callable form's annotations TypeScript infers for an
   * `Object.assign(arrow, literal)` written without type arguments, by the
   * call's span, or why none. */
  readonly assignTypes: Map<string, Answered<{ functionType: TypeTerm; bagType: TypeTerm }>> = new Map();
  /** Local bindings that shadow a binding of an enclosing scope, and every
   * reference TypeScript resolves to one, by the span of the identifier: the
   * name the fragment gives the binding instead (`shadowName`). */
  readonly renames: Map<string, string> = new Map();
  /** The fragment's name of a value binding or reference spelled by `id`:
   * its own text, unless it is or names a shadowing local (`renames`). */
  local(id: Identifier): Within<{ value: "keep"; store: "keep" }, string> {
    return this.renames.get(`${id.getStart(this.file)}:${id.end}`) ?? id.text;
  }
  /** The class whose instance members are being lowered: its own name reads
   * its class binding there (`selfName`). */
  selfClass: { name: string; generic: boolean } | null = null;
  /** The classes lowered so far, by name: what a class extending one reads
   * (`classStmt`). */
  readonly classRecords: Map<string, ClassRecord> = new Map();
  /** The declarators of early bindings (`markEarly`). */
  readonly earlyDecls: Set<Node> = new Set();
  /** The class a method being lowered inherits from: what `super.m(...)`
   * calls. */
  superClass: ClassRecord | null = null;
  /** Calls the reviewed overlay of library globals reads as a test of the
   * calculus, `Array.isArray(e)`, and `e instanceof Array`, by span. */
  readonly globalTests: Set<string> = new Set();
  /** The import bindings of a listed guard of the compiler API's family
   * (HOST-FAMILIES.md, "Calls"), by local name: its kind, its exact tag
   * values and the domain its declared parameter states. */
  readonly hostGuards: Map<string, { domain: TypeTerm; field: string | null; tags: readonly (number | string)[];
    onUndefined: GuardUndefined }> = new Map();
  /** Statement calls of `node:assert/strict`'s `assert` and `ok` read as the
   * calculus's own test, by span. */
  readonly assertionCalls: Set<string> = new Set();
  /** Calls the reviewed overlay reads as a call of an intrinsic,
   * `Promise.resolve(v)`, by span: the intrinsic's name. */
  readonly globalIntrinsics: Map<string, string> = new Map();
  /** Calls the reviewed overlay reads as the global's construct, `Error(m)`,
   * by span. */
  readonly globalConstructs: Set<string> = new Set();
  /** The file's enums by name (SOURCE-CONTRACTS.md, "Enums"), each member's value as
   * TypeScript computes it, once the declaration graph has been read. */
  readonly enums: Map<string, EnumInfo> = new Map();
  /** The enums the file imports, by local name, with their members as the
   * declaration graph read them. */
  readonly importedEnums: Map<string, { members: readonly EnumMemberValue[]; reverse: EnumReverse }> = new Map();
  /** Reads of a `const enum` member TypeScript writes as the member's value,
   * by span: that value. */
  readonly constEnumReads: Map<string, string | number> = new Map();
  /** Reads in an enum member's initializer of a member of the same enum,
   * bare or `E.M`, `E["M"]`, by span, with the member's span. */
  readonly enumMemberReads: Map<string, string> = new Map();
  // Mode of the ordinary function that bound `this`, or no binding. A strict
  // arrow captures its creator's already-converted receiver; it cannot rebind it.
  receiverMode: "strict" | "sloppy" | null = null;
  /* Whether the function whose body is being read is async: its returns
     settle the promise its call returned (`intrinsics.mts`). */
  asyncBody: boolean = false;
  /* Whether that function is a type guard or an assertion function: a
     return of a Boolean by its form is then a condition (`booleanReturn`). */
  guardBody: boolean = false;
  /** Each occurrence of a namespace member (`namespace-members.mts`), a
   * member read or a qualified type name, by its span: the binding it reads. */
  namespaceUses: Map<string, { member: NamespaceMember; use: MemberUse }> = new Map();
  /** The names TypeScript binds to the standard library's declarations
   * alone, among those the gate lowers specially (`libraryNames`), by span. */
  readonly libraryNames: Set<string> = new Set();
  /** The names the file declares nowhere that TypeScript binds to the
   * standard library's `var`s and functions alone, by span. */
  readonly libraryValues: Set<string> = new Set();
  /** The identifiers spelled `undefined` that TypeScript binds to the global
   * `undefined`, by span: those alone read the value `undefined`. */
  readonly globalUndefined: Set<string> = new Set();
  /** The global `Object`s of `Object.assign` calls, which no global value
   * stands for: each is the intrinsic or refused, by span. */
  readonly assignObjects: Set<string> = new Set();

  constructor(file: SourceFile) {
    this.file = file;
  }

  /** The binding a namespace member read or qualified type name reads, or
   * undefined for another node. */
  namespaceMember(node: Node): Within<{ value: "any"; store: "grow" }, string | undefined> {
    return this.namespaceUses.get(this.span(node).join(":"))?.member.local;
  }

  /** Whether TypeScript binds a name to the standard library's
   * declarations alone: `Object` of `Object.assign`, or the member `call`,
   * `apply` or `bind` of a function. A local, an import or a namespace
   * member of that spelling is not. */
  libraryName(node: Node): Within<{ value: "any"; store: "grow" }, boolean> {
    return this.libraryNames.has(this.span(node).join(":"));
  }

  /** The leading `"use strict"` directives of a directive prologue: whether
   * there is one, and how many statements the prologue's "use strict" members
   * occupy, which are dropped since they do nothing else. Another directive
   * stays an ordinary statement. */
  useStrict(statements: readonly Statement[]): Within<{ value: "any"; store: "grow" }, {
    strict: boolean;
    skip: Set<Statement>;
  }> {
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

  hasTypeParam(name: string): Within<{ value: "keep"; store: "keep" }, boolean> {
    return this.typeParamScopes.some((scope) => scope.has(name));
  }

  /** The name a type parameter in scope is emitted under: its spelling, or,
   * for a class's generic method, its member's binder name (`lambda`). */
  typeParamName(name: string): Within<{ value: "any"; store: "keep" }, string> {
    for (const scope of this.typeParamScopes) {
      const emitted = scope.get(name);
      if (emitted !== undefined) return emitted;
    }
    return name;
  }

  /** The qualification a bound declares: the verifier's `Resolvable` or
   * `Awaitable`, by the declaration the file's name binds to, not shadowed by
   * a type parameter. */
  qualificationBound(bound: TypeNode | undefined): Within<{ value: "any"; store: "grow" }, "resolvable" | "awaitable" | null> {
    if (!bound || !ts.isTypeReferenceNode(bound) || !ts.isIdentifier(bound.typeName) ||
        bound.typeArguments?.length) return null;
    const name = bound.typeName.text;
    if (this.hasTypeParam(name) || this.blockTypeAt(bound)) return null;
    return name === "Resolvable" && this.standardResolvable ? "resolvable"
      : name === "Awaitable" && this.standardAwaitable ? "awaitable" : null;
  }

  /** A function declaration's type parameters may be qualified
   * (`qualifiable`): `T extends Resolvable` declares it resolvable, owning
   * its observation and result, `T extends Awaitable` awaitable, owning its
   * observation; neither is a subtype bound. */
  enterTypeParams(
    parameters: readonly TypeParameterDeclaration[] | undefined,
    rename?: (parameter: TypeParameterDeclaration, index: number) => Within<{ value: "any"; store: "grow" }, string>,
    qualifiable: boolean = false,
  ): Within<{ value: "any"; store: "grow" }, TypeParamAst[]> {
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
      this.typeParamScopes = this.typeParamScopes.slice(1);
      this.resolutionScopes = this.resolutionScopes.slice(1);
      throw error;
    }
  }

  leaveTypeParams(): Within<{ value: "any"; store: "grow" }, void> {
    this.resolutionScopes = this.resolutionScopes.slice(1);
    const left = this.typeParamScopes[0];
    this.typeParamScopes = this.typeParamScopes.slice(1);
    if (!left) throw new Error("internal: no type-parameter scope to leave");
  }

  headerTypes<T>(read: () => T): T {
    const outer = this.qualificationHeader;
    this.qualificationHeader = true;
    try { return read(); }
    finally { this.qualificationHeader = outer; }
  }

  enumMembers: typeof classes.enumMembers = classes.enumMembers;

  enumOpen: typeof classes.enumOpen = classes.enumOpen;

  enumObjectTerm: typeof classes.enumObjectTerm = classes.enumObjectTerm;

  enumTerm: typeof classes.enumTerm = classes.enumTerm;

  enumEntries: typeof classes.enumEntries = classes.enumEntries;

  enumStmt: typeof classes.enumStmt = classes.enumStmt;

  /** The enum member initializer being lowered, of an enum with a member
   * known only at run time (`enumStmt`): its enum, members and index. */
  enumInit: { name: string; members: EnumMember[]; index: number } | null = null;

  enumRead: typeof classes.enumRead = classes.enumRead;

  classStmt: typeof classes.classStmt = classes.classStmt;

  classBody: typeof classes.classBody = classes.classBody;

  registerDeclaredType: typeof classes.registerDeclaredType = classes.registerDeclaredType;
  registerEquation: typeof classes.registerEquation = classes.registerEquation;

  /** A failure of the tool: reported as a tool failure, never as a gate
   * refusal, so no verdict on the source follows. The report carries what
   * was thrown as its cause, so it stays a tool failure where it is caught. */
  toolFailure(node: Node | null, failure: ToolFailure, cause: unknown): never {
    const start = node ? node.getStart(this.file) : 0;
    const at = this.file.getLineAndCharacterOfPosition(start);
    throw new Error(toolFailureText(failure, `(line ${at.line + 1}, col ${at.character + 1})`), { cause });
  }

  fail(node: Node | null, message: string): never {
    throw refusal(this.refusal(node, message), node ? this.span(node) : [0, this.file.end]);
  }

  /** The gate's refusal `message`, located at `node`. */
  refusal(node: Node | null, message: string): Within<{ value: "any"; store: "grow" }, string> {
    const start = node ? node.getStart(this.file) : 0;
    const at = this.file.getLineAndCharacterOfPosition(start);
    return `gate: ${message} (line ${at.line + 1}, col ${at.character + 1})`;
  }

  span(node: Node): Within<{ value: "keep"; store: "keep" }, Span> {
    return [node.getStart(this.file), node.end];
  }

  memberKey: typeof classes.memberKey = classes.memberKey;

  staticPrivate: typeof classes.staticPrivate = classes.staticPrivate;

  selfConstruction: typeof classes.selfConstruction = classes.selfConstruction;

  readsClass: typeof classes.readsClass = classes.readsClass;

  staticInitOf: typeof classes.staticInitOf = classes.staticInitOf;

  ownClass: typeof classes.ownClass = classes.ownClass;

  /* ------------------------------------------------------ async, await -- */
  // `async` and `await` are trusted steps, written as calls of intrinsics
  // (`intrinsics.mts`): the call is at `pos`, the intrinsic read at `at`.

  intrinsic(name: string, pos: Span, at: Span, args: Expr[]): Within<{ value: "any"; store: "grow" }, Expr> {
    return { k: "apply", pos, callee: { k: "id", pos: at, name }, args };
  }

  /** A spread argument's operand. Over a string, a `Set`, a `Map` or a host
   * collection iterator, which TypeScript's type of it decides, `...x` is
   * `...%Spread:K%(x)`: the fresh array of the elements its iterator yields
   * (`intrinsics.mts`), the call at the spread, the intrinsic read at `...`.
   * An array is spread as it is. A program's iterable is collected into a
   * fresh array before the statement (`collect`), where that runs its code in
   * its place (`hoistTarget`). */
  spreadOperand(arg: ts.SpreadElement): Within<{ value: "any"; store: "grow" }, Expr> {
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
  writtenSymbol(name: ts.ComputedPropertyName, at: Node): Within<{ value: "any"; store: "grow" }, number | null> {
    const found = this.symbolNames.get(this.span(name.expression).join(":"));
    const symbol = found?.ok ? found.value : null;
    if (typeof symbol !== "number") return null;
    if (this.hostSymbols.has(symbol))
      this.fail(at, "a well-known symbol key other than `Symbol.iterator` and `Symbol.hasInstance` is outside the fragment: it changes how the host treats the object, which the model does not state, and `Symbol.toStringTag` would let it pass for a host collection whose iteration is trusted");
    return symbol;
  }

  /** `await e`: `%Await%(e)`, the intrinsic read at the keyword. Every span
   * an intrinsic call or read is given is a node or a token of the source. */
  awaitExpr(node: ts.AwaitExpression): Within<{ value: "any"; store: "grow" }, Expr> {
    const start = node.getStart(this.file);
    return this.intrinsic(awaitName, this.span(node), [start, start + "await".length],
      [this.expr(node.expression)]);
  }

  /** An async body completes with `return %AsyncComplete%()`: the call spans
   * the block, the intrinsic and the statement its closing brace. Nothing is
   * added to a body that returns on every path. */
  asyncCompletion(block: ts.Block, statements: Stmt[]): Within<{ value: "any"; store: "grow" }, Stmt[]> {
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

  text(node: Node): Within<{ value: "any"; store: "grow" }, string> {
    return this.file.text.slice(node.getStart(this.file), node.end);
  }

  /* ------------------------------------------------------------- types -- */

  /** The type declared in a block TypeScript binds a reference to, if any:
   * it shadows every other meaning of its spelling. */
  blockTypeAt(node: Node): Within<{ value: "any"; store: "grow" }, Answered<BlockType> | undefined> {
    return this.blockTypes.get(this.span(node).join(":"));
  }
  /** Type syntax reads through the one source-term reader, at this record
   * of the gate's hooks. A name is a binder of an enclosing function or a
   * declaration root; every declaration root was resolved by TypeScript's
   * checker. */
  termScope(): TermScope {
    return {
      source: this.file,
      annotation: true,
      awaited: node => this.standardAwaited && ts.isIdentifier(node.typeName) &&
        node.typeName.text === "Awaited" && !this.hasTypeParam("Awaited") && !this.blockTypeAt(node),
      // `Within`, where the file names the verifier's and no type parameter,
      // block type or declaration of the file's shadows it.
      stated: node => this.standardWithin && ts.isIdentifier(node.typeName) && node.typeName.text === "Within" &&
        !this.hasTypeParam("Within") && !this.blockTypeAt(node) && !this.declaredTypes.has("Within"),
      associatedAlias: node => ts.isIdentifier(node.typeName) && !this.hasTypeParam(node.typeName.text) &&
          !this.blockTypeAt(node)
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
        // An imported enum's, at its members as the declaration graph read
        // them, with the reverse keys it decided (`emitted-enum`); the enum
        // named directly or as a namespace member.
        const enumName = (name: Node): string | undefined =>
          ts.isIdentifier(name) ? (this.hasTypeParam(name.text) ? undefined : name.text) : this.namespaceMember(name);
        if (ts.isTypeQueryNode(node) && !node.typeArguments?.length) {
          const named = enumName(node.exprName);
          const imported = named === undefined ? undefined : this.importedEnums.get(named);
          if (imported) return enumMembersTerm(imported.members, span, imported.reverse);
        }
        if (ts.isTypeReferenceNode(node) && ts.isQualifiedName(node.typeName)) {
          const named = enumName(node.typeName.left);
          const imported = named === undefined ? undefined : this.importedEnums.get(named)?.members;
          const member = node.typeName.right.text;
          const found = imported?.find((m) => m.name === member);
          if (imported && !found) return this.fail(node, `${named ?? ""} has no member ${member}`);
          if (found) return found.value === undefined ? { k: "atom", name: "number", span } : literalTerm(found.value, span);
        }
        return null;
      },
      symbol: (name) => {
        const [start, end] = this.span(name);
        const result = this.symbolNames.get(`${start}:${end}`);
        if (result === undefined) return this.fail(name, "a computed key names a symbol constant");
        if (!result.ok) return this.fail(name, result.refused);
        if (typeof result.value === "number") return result.value;
        return this.fail(name, "a computed key naming a literal is no symbol");
      },
      literalKey: (name) => {
        const result = this.symbolNames.get(this.span(name).join(":"));
        return result?.ok && typeof result.value !== "number" ? result.value.literal : null;
      },
      keys: (node) => this.keyType(node),
      modifiers: (node) => this.mappedMembers.get(this.span(node).join(":")) ?? null,
      // A named type's record shape, at the complete declaration document.
      record: (reference, fail) => {
        const records = this.namedRecords();
        return records && recordShape(reference, records, fail);
      },
      // The alias the reference names, as TypeScript resolved it, at every
      // one of its parameters.
      equation: (reference) => {
        const alias = this.aliasEquations.get(classes.identityKey(reference.reference.target));
        if (!alias || reference.args.length !== alias.total) return null;
        return substitute(alias.expression, reference.args);
      },
      computed: (node, span) => {
        const result = this.computedTypes.get(`${span[0]}:${span[1]}`);
        if (!result) return this.fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
        if (!result.ok) return this.fail(node, result.refused);
        return this.settled(result.value, node);
      },
      named: (node, span, read) => {
        const name = ts.isIdentifier(node.typeName) ? node.typeName.text
          : this.namespaceMember(node.typeName) ?? this.fail(node, "type reference outside the fragment");
        const answered = this.blockTypeAt(node);
        if (answered && !answered.ok) return this.fail(node, answered.refused);
        const block = answered?.value;
        // An application of an alias TypeScript computes from its parameters
        // is a computed type, evaluated where it is written: the graph
        // answers a reference only where TypeScript binds it to one.
        const computed = this.computedTypes.get(`${span[0]}:${span[1]}`);
        if (computed) {
          if (!computed.ok) return this.fail(node, computed.refused);
          return this.settled(computed.value, node);
        }
        // A type declared in a block, at the binders it closes over, which
        // TypeScript resolves to themselves here (`blockTypes`).
        if (block) {
          if (block.computed) return this.fail(node, "computed block type evaluation missing");
          const closed = block.captured.map((spelling): TypeTerm => {
            if (!this.hasTypeParam(spelling))
              this.fail(node, `the type ${name} declared in a block closes over ${spelling}, which is not in scope here`);
            return { k: "binder", name: this.typeParamName(spelling), span };
          });
          return this.declaredReference(node, name, span, block, closed, read);
        }
        if (this.enums.has(name) && !this.hasTypeParam(name)) {
          if (node.typeArguments?.length) this.fail(node, "an enum type takes no type arguments");
          return this.enumTerm(name, span);
        }
        // An imported enum's type in the file's annotations: the union of
        // its members' types (`ambient-enum`).
        const imported = this.importedEnums.get(name)?.members;
        if (imported && !this.hasTypeParam(name)) {
          if (node.typeArguments?.length) this.fail(node, "an enum type takes no type arguments");
          const parts = imported.map((m): TypeTerm =>
            m.value === undefined ? { k: "atom", name: "number", span } : literalTerm(m.value, span));
          return parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
        }
        const library = this.libraryTypes.get(name);
        if (library !== undefined && !this.hasTypeParam(name))
          return libraryTerm(library, libraryArguments(library, node.typeArguments ?? [], read,
            part => this.keyType(part)), span,
            message => this.fail(node, message), this.termScope().record);
        const declared = this.declaredTypes.get(name);
        if (declared !== undefined && !this.hasTypeParam(name))
          return this.declaredReference(node, name, span, declared, [], read);
        if (node.typeArguments?.length) this.fail(node, "unknown type alias");
        if (!this.hasTypeParam(name)) this.fail(node, "unknown type parameter");
        return { k: "binder", name: this.typeParamName(name), span };
      },
    };
  }

  /** A reference to a declaration of the graph: its captured arguments
   * (`closed`, a type declared in a block's), the written ones, and the
   * omitted ones completed at them. */
  declaredReference(node: ts.TypeReferenceNode, name: string, span: Span,
      declared: { required: number; total: number; declaration: DeclarationIdentity }, closed: TypeTerm[],
      read: (part: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    const args = node.typeArguments ?? [];
    if (args.length < declared.required || args.length > declared.total) {
      const count = declared.required === declared.total
        ? `${declared.total}`
        : `${declared.required} to ${declared.total}`;
      this.fail(node, `type '${name}' needs ${count} type argument(s)`);
    }
    const omitted: Answered<TypeTerm[]> | undefined = args.length < declared.total
      ? this.completions.get(`${span[0]}:${span[1]}`) : { ok: true, value: [] };
    if (!omitted) return this.fail(node, `type '${name}' has no completion of its omitted arguments`);
    if (!omitted.ok) return this.fail(node, omitted.refused);
    return { k: "reference", reference: { name, span,
      arguments: args.map(arg => this.span(arg)), target: declared.declaration },
      args: [...closed, ...args.map(read), ...omitted.value.map(t => this.settled(t, node))], span };
  }

  /** The complete declaration document's definitions, as a named type's
   * record shape is read from them (`NamedRecords`); null before it is
   * complete. */
  namedRecords(): Within<{ value: "any"; store: "grow" }, NamedRecords | null> {
    const definitions = this.recordDefinitions;
    if (!definitions) return null;
    return { definition: id => definitions.get(definitionKey(id)), record: id => this.recordKeys.has(definitionKey(id)) };
  }

  /** A term the declaration graph read while it was collected, with each
   * mapped type it deferred at a named type expanded at the complete
   * document (`settleTerm`); a refusal located at `node`. */
  settled(term: TypeTerm, node: Node): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    const records = this.namedRecords();
    if (!records) return term;
    return settleTerm(term, records, "the source", (_where, error) => {
      passToolFailure(error);
      return this.fail(node, messageOf(error));
    });
  }

  keyType(node: Node): Within<{ value: "any"; store: "grow" }, TypeTerm | null> {
    const term = this.keyTypes.get(this.span(node).join(":"));
    return term ? this.settled(term, node) : null;
  }

  typeOf(node: TypeNode | undefined, at: Node | null = null): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    return typeTerm(this.termScope(), node, at);
  }

  /** A definition's written result: its statement of the definition's
   * effect, `Within<F, T>`, and the result annotation it states it of
   * (`statedResult`); no statement where it writes none. */
  statedResult(node: TypeNode | undefined, at: Node): Within<{ value: "any"; store: "grow" }, { stated: StatedEffect | null; result: TypeNode | undefined }> {
    return statedResult(this.termScope(), node, at);
  }

  /** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
   * value bound when a call omits that position. The fragment carries the
   * union, so nothing downstream needs a second representation of optionality.
   * A call may omit a trailing position exactly when its contract admits
   * `undefined`; declared arity is not observable in this fragment. */
  optionalTypeOf(node: TypeNode | undefined, at: Node): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    return optionalTerm(this.typeOf(node, at), this.span(at));
  }

  /** A closure parameter's contract: its annotation, or, without one, the
   * type TypeScript gives it from its context (an optional one's includes
   * `undefined` already). That type is a proposal like any claim: the body
   * is checked at it, and the closure's signature wherever the closure
   * goes, the call offering it included. Its declarations belong to the shared
   * declaration graph, and its type parameters are in scope. */
  closureParamType(p: ts.ParameterDeclaration): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    if (p.type || p.dotDotDotToken) return p.questionToken ? this.optionalTypeOf(p.type, p) : this.typeOf(p.type, p);
    const answered = this.contextualParams.get(this.span(p.name).join(":"));
    if (!answered) return this.typeOf(undefined, p);
    if (!answered.ok) return this.fail(p, answered.refused);
    const found = this.settled(answered.value, p);
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
  restType(p: ParameterDeclaration): Within<{ value: "any"; store: "grow" }, TypeTerm> {
    const type = restTerm(this.termScope(), this.typeOf(p.type, p));
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
  moduleRestType(p: ParameterDeclaration, node: FunctionDeclaration): TypeTerm {
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

  expr: typeof expressions.expr = expressions.expr;

  objectFields: typeof expressions.objectFields = expressions.objectFields;

  optionalChain: typeof expressions.optionalChain = expressions.optionalChain;

  chainLink: typeof expressions.chainLink = expressions.chainLink;

  refuseReceiverForm: typeof expressions.refuseReceiverForm = expressions.refuseReceiverForm;

  knownLocal: typeof expressions.knownLocal = expressions.knownLocal;

  /** Each scope's bindings by name (`resolve`), built on the first call. */
  bindings: Map<Node, Map<string, Node>> | null = null;
  resolve: typeof expressions.resolve = expressions.resolve;

  confined: typeof expressions.confined = expressions.confined;

  localArrow: typeof expressions.localArrow = expressions.localArrow;

  memberOf: typeof expressions.memberOf = expressions.memberOf;

  moduleFunction: typeof expressions.moduleFunction = expressions.moduleFunction;

  memberMayBeWritten: typeof expressions.memberMayBeWritten = expressions.memberMayBeWritten;

  localValues: typeof expressions.localValues = expressions.localValues;

  letWrites: typeof expressions.letWrites = expressions.letWrites;

  update: typeof expressions.update = expressions.update;

  template: typeof expressions.template = expressions.template;

  hasInstanceClass: typeof expressions.hasInstanceClass = expressions.hasInstanceClass;

  hasInstanceAlong: typeof expressions.hasInstanceAlong = expressions.hasInstanceAlong;

  staticHasInstance: typeof expressions.staticHasInstance = expressions.staticHasInstance;

  binary: typeof expressions.binary = expressions.binary;

  /* ----------------------------------------------------------- closures -- */
  // A closure body is an expression in the calculus. A block-bodied one is
  // lowered here, once, so the verifier never has to guess how statements
  // inside a closure become one: the parser owns that translation because it
  // owns what the source means.

  lambda: typeof expressions.lambda = expressions.lambda;

  /* -------------------------------------------------------- statements -- */

  /* `const pattern = init;`. One declarator; object and array patterns,
     nested, with identifier keys, defaults, holes and an array rest: what the
     lowering states. */
  patternStmt: typeof statements.patternStmt = statements.patternStmt;

  protocolPattern: typeof statements.protocolPattern = statements.protocolPattern;

  collectStep: typeof statements.collectStep = statements.collectStep;

  closeStatements: typeof statements.closeStatements = statements.closeStatements;

  collect: typeof statements.collect = statements.collect;

  hoistTarget: typeof statements.hoistTarget = statements.hoistTarget;
  readCannotThrow: typeof statements.readCannotThrow = statements.readCannotThrow;
  readScope: typeof statements.readScope = statements.readScope;

  unassigned: typeof statements.unassigned = statements.unassigned;

  /* Each default of a declaration's patterns, in binding order, reads none
     of the declaration's own names not yet initialized: JavaScript throws
     there (the temporal dead zone), where the lowering would read whatever
     outer binding has the name. */
  initializedBefore: typeof statements.initializedBefore = statements.initializedBefore;

  /* Whether evaluating `e` runs no code but its own and writes nothing but a
     local: a literal, a name, a field read (the heap has data properties
     only), a read at a literal key, `!`, `typeof`, `void`, a sign of a
     literal, `===`, `!==`, `&&`, `||`, `??`, a comma, a conditional, an
     assignment of a local, an array or object literal of such parts, a
     closure's creation. Anything else may call, convert an object or write a
     field. */
  inert: typeof statements.inert = statements.inert;

  /* The defaults a binding pattern runs, at any depth. */
  patternDefaults: typeof statements.patternDefaults = statements.patternDefaults;

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
  steppedPattern: typeof statements.steppedPattern = statements.steppedPattern;

  /* An array assignment's elements, as `steppedPattern` reads them. */
  assignedSteps: typeof statements.assignedSteps = statements.assignedSteps;

  /* What a binding name or pattern binds. An object pattern reads identifier
     keys; its rest binds a fresh object holding the source's other own
     enumerable properties. An array pattern's hole is a position no element
     names; `fresh` says its source is an array literal (`steppedPattern`). */
  pattern: typeof statements.pattern = statements.pattern;

  /* A branch or loop body. TypeScript allows a single statement where a block
     could be written, and the two mean the same thing here: a lexical
     declaration cannot be an unbraced body, so no binding's scope depends on
     the braces. */
  block: typeof statements.block = statements.block;

  statements: typeof statements.statements = statements.statements;

  hoisting: typeof statements.hoisting = statements.hoisting;

  markEarly: typeof statements.markEarly = statements.markEarly;

  letPattern: typeof statements.letPattern = statements.letPattern;
  letPatternOf: typeof statements.letPatternOf = statements.letPatternOf;
  declarator: typeof statements.declarator = statements.declarator;
  mutableList: typeof statements.mutableList = statements.mutableList;
  lexicalList: typeof statements.lexicalList = statements.lexicalList;
  declarationsOf: typeof statements.declarationsOf = statements.declarationsOf;

  token: typeof statements.token = statements.token;

  forStmt: typeof statements.forStmt = statements.forStmt;

  forInStmt: typeof statements.forInStmt = statements.forInStmt;

  protocolForOf: typeof statements.protocolForOf = statements.protocolForOf;
  forOfPattern: typeof statements.forOfPattern = statements.forOfPattern;

  sites: typeof statements.sites = statements.sites;

  protocolStart: typeof statements.protocolStart = statements.protocolStart;

  protocolStep: typeof statements.protocolStep = statements.protocolStep;

  switchStmt: typeof statements.switchStmt = statements.switchStmt;

  tryStmt: typeof statements.tryStmt = statements.tryStmt;

  stmt: typeof statements.stmt = statements.stmt;

  declarations: typeof statements.declarations = statements.declarations;

  neverAssigned: typeof statements.neverAssigned = statements.neverAssigned;

  controlStmt: typeof statements.controlStmt = statements.controlStmt;

  /* --------------------------------------------------------- functions -- */

  functionDecl: typeof statements.functionDecl = statements.functionDecl;

  guardOf: typeof guards.guardOf = guards.guardOf;
}

/** A program module a lowered file imports a function from: its file, and
 * its identity in the declaration documents (`DeclarationIdentity.module`). */
export type ImportedModule = { absolute: string; location: string };

/** An imported module to lower: its file, its identity in the importer's
 * documents, the project the run reads, and the run's tag selection of each
 * host family (HOST-FAMILIES.md, "Residuals"), where the checked file made
 * one. */
export type ModuleRequest = { absolute: string; location: string; tsconfigPath: string | undefined;
  selection: ReadonlyMap<string, readonly TagValue[]> | undefined };
/** An imported module lowered, as `M`, with the program modules it imports
 * functions from; or the gate's refusal of it. */
export type LoweredModule<M> = { module: M; imported: ImportedModule[]; refused?: never } | { refused: string };
/** The name of a module stage's read of the run's selection of the host
 * family `marker`. */
export const selectionRead = (marker: string): string => `selection/${marker}`;
/** The family a read `selectionRead` names, or null for another name. */
export const selectionMarker = (name: string): string | null =>
  name.startsWith("selection/") ? name.slice("selection/".length) : null;
/** A module's entry as text, with the refusal of its first string that is
 * not well-formed Unicode, if it has one. */
export type ModuleText = { text: string; illFormed: string | null };

/**
 * The fragment of `file`, with every program module it imports a function
 * from, directly or through another such module, lowered as a run of that
 * module alone lowers it, under the same project (`modules`). A module whose
 * declarations or top-level code the gate refuses is left out: its imports
 * stay at their declared types. After a tool failure the parser's compiler
 * is released: its channel's next reply may be unreadable, and the next
 * parse opens another.
 */
export function parseFile(file: string, carriesContext: boolean = false,
  tsconfigPath?: string, resolutionFile: string = file,
  seen?: (diagnostic: SeenDiagnostic) => void): Ast {
  return failingAsTool(file, () => {
    const { ast, modules } = parseModules(file, carriesContext, tsconfigPath, resolutionFile, seen, lowerModule);
    const whole = { ...ast, modules };
    // A source string the wire cannot carry as itself (SOURCE-FRAGMENT.md).
    requireWellFormedText(JSON.stringify(whole), "gate");
    return whole;
  });
}

/** Diagnostic syntax has an envelope disjoint from the Fragment wire.
 * Only this entry point installs recovery; ordinary parsing owns a plain gate. */
export function diagnosticFragment(file: string, tsconfigPath: string | undefined):
    { diagnostic: Ast | null; occurrences: GateOccurrence[]; incomplete: string | null } {
  const occurrences: GateOccurrence[] = [];
  return failingAsTool(file, () => {
    try {
      const { ast } = lowerFile(file, false, tsconfigPath, file, undefined, null, {}, occurrences);
      return { diagnostic: ast, occurrences, incomplete: null };
    } catch (error) {
      passToolFailure(error);
      const refused = refusalOf(error);
      if (!refused) throw error;
      occurrences.push({ pos: refused.pos, region: [0, readText(file).length], reason: refused.message,
        recovery: "shared source preparation unavailable" });
      return { diagnostic: null, occurrences, incomplete: refused.message };
    }
  });
}

/** The fragment of `file` as `parseFile` gives it, as its JSON text, each
 * imported module lowered by `lower` (the parse stage's: `module`, an
 * observed stage of its own) and spliced into the document as its text, in
 * the order the run reaches it: the bytes `JSON.stringify` writes of the
 * same value. The first string that is not well-formed Unicode is refused
 * in document order, as `parseFile` refuses it. */
export function parseFragment(file: string, tsconfigPath: string | undefined, resolutionFile: string,
  seen: (diagnostic: SeenDiagnostic) => void, lower: (request: ModuleRequest) => LoweredModule<ModuleText>): string {
  return failingAsTool(file, () => {
    const { ast, modules } = parseModules(file, false, tsconfigPath, resolutionFile, seen, lower);
    const text = JSON.stringify(ast);
    requireWellFormedText(text, "gate");
    for (const m of modules) if (m.illFormed !== null) throw Error(m.illFormed);
    const empty = `,"modules":[]}`;
    if (!text.endsWith(empty)) throw Error("tool failure: the fragment does not end with its modules");
    return `${text.slice(0, -empty.length)},"modules":[${modules.map((m) => m.text).join(",")}]}`;
  });
}

/** `run`, a parse of `file`; after a tool failure the parser's compiler
 * released, and a failure no read located reported as one, in the file. */
function failingAsTool<T>(file: string, run: () => T): T {
  try {
    return run();
  } catch (error) {
    const failure = toolFailureOf(error);
    if (!failure) throw error;
    release({ error });
    if (messageOf(error).startsWith("tool failure:")) throw error;
    throw new Error(toolFailureText(failure, `(in ${file})`), { cause: error });
  }
}

/** The lowering of an imported module as a run of that module alone lowers
 * it, in a parser compiler of its own, opened at the module's directory and
 * released after it; the gate's refusal of it, or, on a tool failure, that
 * failure reported in the module. */
export function lowerModule(request: ModuleRequest): LoweredModule<ModuleAst> {
  release(null);
  let lowered: Lowered;
  try {
    const selection = request.selection;
    // Each read of the run's selection, by family, is a read of the stage's
    // named input (STAGE-STORE.md, "Shared work").
    lowered = lowerFile(request.absolute, false, request.tsconfigPath, request.absolute, undefined,
      request.location, selection ? { given: (marker) => {
        const tags = selection.get(marker);
        noteInput(selectionRead(marker), JSON.stringify(tags ?? null) ?? "null");
        return tags;
      } } : {});
  } catch (error) {
    // The gate's refusal leaves the module out; a tool failure is no
    // refusal, and is reported in that module.
    const failure = toolFailureOf(error);
    if (!failure) return { refused: messageOf(error) };
    release({ error });
    throw new Error(toolFailureText(failure, `(lowering the imported module ${request.location})`), { cause: error });
  } finally {
    release(null);
  }
  // A module's lowering is its entry (`location` is given).
  if (!lowered.module) throw Error("tool failure: an imported module lowered without its entry");
  return { module: lowered.module, imported: lowered.imported };
}

/** `lowerModule`'s lowering with the module's entry as text. */
export function lowerModuleText(request: ModuleRequest): LoweredModule<ModuleText> {
  const lowered = lowerModule(request);
  if (lowered.refused !== undefined) return lowered;
  const text = JSON.stringify(lowered.module);
  return { module: { text, illFormed: wellFormedTextRefusal(text, "gate") }, imported: lowered.imported };
}

/** The fragment of `file` without its modules, and each program module it
 * imports a function from, directly or through another, as `lower` lowers
 * it, in the order the run reaches it; a module `lower` refuses left out. */
function parseModules<M>(file: string, carriesContext: boolean, tsconfigPath: string | undefined,
  resolutionFile: string, seen: ((diagnostic: SeenDiagnostic) => void) | undefined,
  lower: (request: ModuleRequest) => LoweredModule<M>): { ast: Ast; modules: M[] } {
  // One tag selection of each host family for the run (HOST-FAMILIES.md,
  // "Residuals"): the checked file's, every imported module lowered with it.
  let selection: ReadonlyMap<string, readonly TagValue[]> | undefined;
  const main = lowerFile(file, carriesContext, tsconfigPath, resolutionFile, seen, null, { selected: s => { selection = s; } });
  // The file's parser compiler is released before any module is lowered: a
  // module's lowering uses none of its state, and a stage nested in this one
  // holds the ledger of every compiler it uses (STAGE-STORE.md, "Shared
  // work").
  release(null);
  const modules: M[] = [];
  const done = new Set<string>();
  const work = [...main.imported];
  for (let next = work.shift(); next; next = work.shift()) {
    if (done.has(next.location)) continue;
    done.add(next.location);
    const lowered = lower({ absolute: next.absolute, location: next.location, tsconfigPath, selection });
    if (lowered.refused !== undefined) continue;
    modules.push(lowered.module);
    work.push(...lowered.imported);
  }
  return { ast: main.ast, modules };
}

/** A lowered file: its fragment, the module entry it is as an imported
 * module, and the program modules it imports functions from. */
type Lowered = { ast: Ast; module: ModuleAst | null; imported: ImportedModule[] };

/** The module with each declaration of `from` named by `to`, each written
 * application's `site` in `from` sited in `to`, and each binder name a
 * declaration of `from` gives (`T@from:offset`) given by `to`: in a binder's
 * declaration (a type parameter's `name` and its resolution slots) and in a
 * binder term's `name`, and nowhere else, so a literal type or a property key
 * spelling such a name keeps it. An imported module's own declarations, which
 * its lowering names by its path, named by its identity in the importer's
 * documents. */
function renamedModule(module: ModuleAst, from: string, to: string): ModuleAst {
  const name = (x: string): string => x.split(`@${from}:`).join(`@${to}:`);
  const identity = (id: DeclarationIdentity): DeclarationIdentity => id.module === from ? { ...id, module: to } : id;
  const slots = (r: ResolutionSlots | null): ResolutionSlots | null =>
    r && { ...r, observation: name(r.observation), result: r.result === null ? null : name(r.result) };
  const node = (t: TypeTerm): TypeTerm => {
    switch (t.k) {
      case "binder": return { ...t, name: name(t.name) };
      case "reference": return { ...t, reference: { ...t.reference, target: identity(t.reference.target) } };
      case "scheme": return { ...t, binders: t.binders.map(b => ({ ...b, name: name(b.name), resolution: slots(b.resolution) })) };
      default: return t;
    }
  };
  const term = (t: TypeTerm): TypeTerm => mapTypeParts(node(t), term);
  const param = (p: TypeParamAst): TypeParamAst =>
    ({ ...p, name: name(p.name), bound: p.bound && term(p.bound), resolution: slots(p.resolution) });
  const site = (at: string): string => at.startsWith(`${from}#`) ? `${to}${at.slice(from.length)}` : at;
  const parts = deepPartMap(term, param);
  return { ...module, declarations: mapDocument(module.declarations, { type: term, param, identity, site }),
    init: module.init.map(parts.stmt), functions: module.functions.map(f => mapFunctionParts(f, parts)) };
}

function lowerFile(file: string, carriesContext: boolean,
  tsconfigPath: string | undefined, resolutionFile: string,
  seen: ((diagnostic: SeenDiagnostic) => void) | undefined, location: string | null,
  family: { given?: (marker: string) => readonly TagValue[] | undefined;
    selected?: (selection: ReadonlyMap<string, readonly TagValue[]>) => void },
  diagnostic?: GateOccurrence[]): Lowered {
  const absolute = resolve(file);
  const text = readText(absolute);
  const { file: source, checker } = openFile(absolute, text);
  const gate = new Gate(source);
  if (diagnostic) recoverGate(gate, diagnostic);
  // The members read through namespace imports, each a binding of its own.
  const members = namespaceMembers(source, checker, (node, message) => gate.fail(node, message));
  gate.namespaceUses = memberUses(members, source);
  const memberNodes = [...gate.namespaceUses.values()].map(({ use }) => use.node);
  // Each `undefined` the file reads, decided by what TypeScript binds it to.
  const undefinedNodes: Identifier[] = [];
  const findUndefined = (node: Node): void => {
    if (ts.isTypeNode(node)) return;
    if (ts.isIdentifier(node) && node.text === "undefined") undefinedNodes.push(node);
    node.forEachChild(findUndefined);
  };
  findUndefined(source);
  checker.getSymbolAtLocation(undefinedNodes).forEach((symbol, i) => {
    const node = undefinedNodes[i];
    if (node && symbol && checker.isUndefinedSymbol(symbol)) gate.globalUndefined.add(gate.span(node).join(":"));
  });
  const aliasNodes: TypeAliasDeclaration[] = [];
  const interfaceNodes: InterfaceDeclaration[] = [];
  const classNodes: ClassDeclaration[] = [];
  const fnNodes: FunctionDeclaration[] = [];
  const importNodes: ImportDeclaration[] = [];
  const enumNodes: ts.EnumDeclaration[] = [];
  // Top-level code other than declarations: the module's initialization, run
  // once, in order, after its function declarations are instantiated.
  const initNodes: Statement[] = [];
  // The names an export list exports (`export { x }`, `export { x as y }`).
  const exportedNames = new Set<string>(source.statements.flatMap(st =>
    ts.isExportDeclaration(st) && !st.moduleSpecifier && st.exportClause && ts.isNamedExports(st.exportClause)
      ? st.exportClause.elements.map(e => (e.propertyName ?? e.name).text) : []));
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
    if (isTypeAlias(s)) aliasNodes.push(s);
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
      // A module constant is read by functions at its annotation. A module
      // `let` the module does not export is a module cell (SOURCE-ELABORATION.md,
      // "Module cells"): an early binding of the module's scope, whatever
      // its mentions. A `var`, and an exported `let`, a live binding an
      // importer reads, are outside the fragment.
      const list = s.declarationList;
      if (!(list.flags & (ts.NodeFlags.Const | ts.NodeFlags.Let)))
        gate.fail(s, "a module-level `var` is outside the fragment");
      if (list.flags & ts.NodeFlags.Let) {
        if (s.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword))
          gate.fail(s, "an exported `let` is a live binding importers read, outside the fragment");
        for (const d of list.declarations) {
          if (!ts.isIdentifier(d.name)) return gate.fail(d, "a module-level `let` pattern is outside the fragment");
          // The module's units read it: a unit boundary, whose type is
          // written.
          if (!d.type)
            gate.fail(d, "a module `let` is a binding the module's units read, a unit boundary: its type is written (an annotation)");
          if (exportedNames.has(d.name.text))
            gate.fail(d, "an exported `let` is a live binding importers read, outside the fragment");
          gate.earlyDecls.add(d);
        }
      }
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
  let declarations: Ast["declarations"] = { roots: [], definitions: [], values: [], symbols: [], applications: [] };
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
  const imported = new Set<string>(importNodes.flatMap(node => {
    const bindings = node.importClause?.namedBindings;
    const named = !bindings ? [] : ts.isNamedImports(bindings) ? bindings.elements.map(e => e.name.text) : [bindings.name.text];
    const name = node.importClause?.name;
    return name ? [name.text, ...named] : named;
  }));
  const rooted = new Set<string>([
    ...imported,
    ...[...aliasNodes, ...interfaceNodes, ...classNodes, ...enumNodes].flatMap(node => node.name ? [node.name.text] : []),
  ]);
  // The names the types declared in the file's blocks bind, and the
  // references outside a type declaration spelling one: TypeScript decides
  // which it binds to such a declaration (`blockTypes`, SOURCE-CONTRACTS.md,
  // "Block-scoped type declarations"). A declaration's body is the graph's
  // to read.
  const blockNames = new Set<string>();
  const findBlockTypes = (node: Node): void => {
    if ((isTypeAlias(node) || ts.isInterfaceDeclaration(node)) && node.parent &&
        !ts.isSourceFile(node.parent))
      blockNames.add(node.name.text);
    node.forEachChild(findBlockTypes);
  };
  findBlockTypes(source);
  const blockReference = (node: Node): node is ts.TypeReferenceNode =>
    ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && blockNames.has(node.typeName.text);
  const blockNodes: ts.TypeReferenceNode[] = [];
  const findBlockReferences = (node: Node): void => {
    if (isTypeAlias(node) || ts.isInterfaceDeclaration(node)) return;
    if (blockReference(node)) blockNodes.push(node);
    node.forEachChild(findBlockReferences);
  };
  if (blockNames.size) findBlockReferences(source);
  // A spelling a block's type may bind is listed at every reference, since
  // its first one may be bound to that block's type.
  const globalNodes: Identifier[] = [];
  const findGlobals = (node: Node): void => {
    const typeName = ts.isTypeReferenceNode(node) ? node.typeName : null;
    if (typeName && ts.isIdentifier(typeName) && !rooted.has(typeName.text) &&
        (blockNames.has(typeName.text) || !globalNodes.some(g => g.text === typeName.text)))
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
    if (ts.isTypeNode(node) || ts.isInterfaceDeclaration(node) || isTypeAlias(node)) return;
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
        ts.isInterfaceDeclaration(node) || isTypeAlias(node) || ts.isHeritageClause(node))
      return;
    if (ts.isIdentifier(node) && !bound.has(node.text) && node.text !== "undefined") {
      const parent = node.parent;
      // `Object.assign(…)` is a call form; `Object.assign` read otherwise is a
      // read of `Object` as a value, which no overlay entry admits.
      const intrinsic = node.text === "Object" && ts.isPropertyAccessExpression(parent) &&
        parent.expression === node && parent.name.text === "assign" &&
        ts.isCallExpression(parent.parent) && parent.parent.expression === parent;
      if (intrinsic) gate.assignObjects.add(gate.span(node).join(":"));
      if (childOf(parent, "name") !== node && childOf(parent, "propertyName") !== node &&
          childOf(parent, "label") !== node && !intrinsic)
        globalValueNodes.push(node);
    }
    node.forEachChild(findGlobalValues);
  };
  if (!carriesContext) findGlobalValues(source);
  // The module's `import.meta`, a value the declaration graph reads at the
  // members the references select.
  const importMetaNodes: ts.MetaProperty[] = [];
  const findImportMeta = (node: Node): void => {
    if (ts.isTypeNode(node)) return;
    if (ts.isMetaProperty(node) && node.keywordToken === ts.SyntaxKind.ImportKeyword) importMetaNodes.push(node);
    node.forEachChild(findImportMeta);
  };
  if (!carriesContext) findImportMeta(source);
  // An array reaches `Array.prototype`, whose contract then joins the graph;
  // the first array the file writes stands for it. `Array<T>` is written by
  // name: if TypeScript binds the name elsewhere, the contract is unused.
  let firstArray: Node | undefined;
  const findArray = (node: Node): void => {
    if (firstArray) return;
    const arrayReference = ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) &&
      (node.typeName.text === "Array" || node.typeName.text === "ReadonlyArray");
    // A regex's matches and splits are arrays. A string's `split` is one
    // too, which the declaration graph decides from the receiver's type.
    if (ts.isArrayTypeNode(node) || ts.isTupleTypeNode(node) || ts.isArrayLiteralExpression(node) || arrayReference ||
        ts.isForOfStatement(node) || (ts.isParameterDeclaration(node) && !!node.dotDotDotToken) ||
        node.kind === ts.SyntaxKind.RegularExpressionLiteral) {
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
  const earlyCandidate = (block: ts.Block): boolean => {
    const declared = new Map<string, ts.VariableDeclaration>();
    for (const st of block.statements)
      if (ts.isVariableStatement(st) && st.declarationList.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))
        for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name)) declared.set(d.name.text, d);
    if (!declared.size) return false;
    const visit = (n: Node, created: number | null): boolean => {
      if (ts.isTypeNode(n)) return false;
      if (ts.isIdentifier(n)) {
        const parent = n.parent;
        if (parent && (((ts.isPropertyAccessExpression(parent) && parent.name === n) ||
            ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
              ts.isPropertySignatureDeclaration(parent)) && parent.name === n)))) return false;
        const d = declared.get(n.text);
        const at = created ?? n.getStart(source);
        if (!d || n === d.name || at >= d.end) return false;
        let literal: Node | undefined = d.initializer;
        while (literal && ts.isParenthesizedExpression(literal)) literal = literal.expression;
        return !(literal && (ts.isArrowFunction(literal) || ts.isFunctionExpression(literal)) &&
          n.getStart(source) >= literal.getStart(source) && n.end <= literal.end);
      }
      const inner = created ?? (ts.isFunctionDeclaration(n) ? -1
        : ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n) ? n.getStart(source) : null);
      return n.forEachChild((c) => visit(c, inner) || undefined) ?? false;
    };
    return block.statements.some((st) => visit(st, null));
  };
  const findAsync = (node: Node): void => {
    const add = (...names: string[]) => {
      firstAsync ??= node;
      names.forEach(name => intrinsicNames.add(name));
    };
    if (ts.isAwaitExpression(node)) add(awaitName);
    // A block whose `let` or `const` may be mentioned before its
    // initialization (`markEarly`, by spelling here) throws through
    // `%ThrowUninitialized%` where a checked access finds it so.
    if (ts.isBlock(node) && earlyCandidate(node)) add(throwUninitializedName);
    // A module `let` is a module cell, every mention a checked access.
    if (ts.isVariableStatement(node) && node.parent && ts.isSourceFile(node.parent) &&
        node.declarationList.flags & ts.NodeFlags.Let) add(throwUninitializedName);
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
  // The names the gate lowers specially where they are the standard
  // library's: TypeScript decides (`libraryName`).
  const libraryNameNodes: Node[] = [];
  // The names read as values, which a hoisted spread may pass where the
  // file declares them nowhere: TypeScript decides which are the standard
  // library's `var`s and functions (`libraryValue`). A spread of a program's
  // iterable is a reason to read the declarations; these names alone are
  // not.
  const libraryValueNodes: Node[] = [];
  const findLibraryNames = (node: Node): void => {
    if (ts.isIdentifier(node) && node.parent && !ts.isTypeNode(node.parent) &&
        !(ts.isPropertyAccessExpression(node.parent) && node.parent.name === node) &&
        !((ts.isPropertyAssignment(node.parent) || ts.isVariableDeclaration(node.parent) ||
          ts.isParameterDeclaration(node.parent) || ts.isFunctionDeclaration(node.parent) ||
          ts.isMethodDeclaration(node.parent) || ts.isClassDeclaration(node.parent)) && node.parent.name === node))
      libraryValueNodes.push(node);
    // A class extending `Error`: TypeScript decides it is the standard one.
    if (ts.isExpressionWithTypeArguments(node) && node.parent && ts.isHeritageClause(node.parent) &&
        ts.isIdentifier(node.expression) && node.expression.text === "Error")
      libraryNameNodes.push(node.expression);
    if (ts.isPropertyAccessExpression(node) && ts.isIdentifier(node.name)) {
      if (["call", "apply", "bind"].includes(node.name.text)) libraryNameNodes.push(node.name);
      if (node.name.text === "assign" && ts.isIdentifier(node.expression) && node.expression.text === "Object")
        libraryNameNodes.push(node.expression, node.name);
    }
    node.forEachChild(findLibraryNames);
  };
  if (!carriesContext) findLibraryNames(source);
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
  // Element reads `e[k]`, links of an optional chain (`r?.[k]`, `r?.a[k]`)
  // among them, other than a write's target and a call's callee, whose call
  // passes the object as its receiver: TypeScript's types of the object and
  // the key decide whether `%ElementAt%` or `%ByteAt%` reads it.
  const elementReadNodes: Node[] = [];
  const findElementReads = (node: Node): void => {
    if (ts.isElementAccessExpression(node) && !writtenElement(node) && !callTarget(node))
      elementReadNodes.push(node);
    node.forEachChild(findElementReads);
  };
  if (!carriesContext) findElementReads(source);
  // Reads `e.length` other than a write's target: TypeScript's type of the
  // object decides whether `%ByteLength%` reads it.
  const lengthReadNodes: Node[] = [];
  const findLengthReads = (node: Node): void => {
    if (ts.isPropertyAccessExpression(node) && ts.isIdentifier(node.name) && node.name.text === "length" &&
        !node.questionDotToken && !writtenElement(node))
      lengthReadNodes.push(node);
    node.forEachChild(findLengthReads);
  };
  if (!carriesContext) findLengthReads(source);
  // Reads `e.k` at a key some `"k" in o` test of the file writes, other than
  // a write's target and a call's callee, at a key no member of
  // `Object.prototype` names: TypeScript's type of the object decides
  // whether `%Read:k%` reads it (an open read).
  const inLiteralKeys = new Set(inKeyNodes.flatMap(key => ts.isStringLiteral(key) ? [key.text] : []));
  const openReadNodes: Node[] = [];
  const findOpenReads = (node: Node): void => {
    if (ts.isPropertyAccessExpression(node) && ts.isIdentifier(node.name) && inLiteralKeys.has(node.name.text) &&
        !objectProtoKeys.has(node.name.text) && !node.questionDotToken && !writtenElement(node) && !callTarget(node))
      openReadNodes.push(node);
    node.forEachChild(findOpenReads);
  };
  if (!carriesContext && inLiteralKeys.size) findOpenReads(source);
  // Regular expression literals: each is a call of the intrinsic its shape
  // names, which the declaration graph lists.
  const regexpNodes: Node[] = [];
  const findRegExps = (node: Node): void => {
    if (node.kind === ts.SyntaxKind.RegularExpressionLiteral) regexpNodes.push(node);
    node.forEachChild(findRegExps);
  };
  if (!carriesContext) findRegExps(source);
  // Calls of the string methods that dispatch to an object argument: their
  // types decide whether the call is `%Dispatch:m%`.
  const dispatchNodes: Node[] = [];
  const findDispatches = (node: Node): void => {
    if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
        isDispatchMethod(node.expression.name.text) && node.arguments.length > 0 && !node.questionDotToken &&
        !node.expression.questionDotToken)
      dispatchNodes.push(node);
    node.forEachChild(findDispatches);
  };
  if (!carriesContext) findDispatches(source);
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
    const assign = callableAssign(node);
    if (assign && !assign.call.typeArguments) assignNodes.push(node);
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
  const mappedNodes: Node[] = [];
  // The file's aliases TypeScript computes from their parameters
  // (`computedAlias`): an application of one is a computed type too.
  const localAlias = (reference: ts.TypeReferenceNode): TypeAliasDeclaration | null => {
    const typeName = reference.typeName;
    return ts.isIdentifier(typeName) ? aliasNodes.find(a => a.name.text === typeName.text) ?? null : null;
  };
  const computedAliases = new Set(aliasNodes.filter(a => computedAlias(a, localAlias)).map(a => a.name.text));
  const findComputed = (node: Node): void => {
    if (isTypeAlias(node) || ts.isInterfaceDeclaration(node)) return;
    if (ts.isTypeNode(node) && (computedForm(node) !== null ||
        (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && computedAliases.has(node.typeName.text) &&
          !enclosingBinders(node).includes(node.typeName.text)))) {
      computedNodes.push(node);
      return;
    }
    // The declaration graph decides which named types have computed
    // equations or members, including defaulted applications with no
    // arguments written. Block references also retain their captured scope.
    if ((ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) &&
        !enclosingBinders(node).includes(node.typeName.text)) || blockReference(node))
      computedNodes.push(node);
    // So does the computed key of a class method or an object literal's
    // property or method, `[Symbol.iterator]() { … }`.
    if (ts.isComputedPropertyName(node) && node.parent &&
        (ts.isPropertySignatureDeclaration(node.parent) || ts.isMethodSignatureDeclaration(node.parent) ||
          ts.isMethodDeclaration(node.parent) || ts.isPropertyAssignment(node.parent)))
      symbolNameNodes.push(node.expression);
    // A mapped type's keys, and a global generic's arguments, which may be
    // a library mapped type's keys, `Record<K, V>`: TypeScript computes them.
    if (ts.isMappedTypeNode(node) && node.typeParameter.constraint) keyTypeNodes.push(node.typeParameter.constraint);
    if (ts.isMappedTypeNode(node) && node.typeParameter.constraint && ts.isTypeOperatorNode(node.typeParameter.constraint) &&
        node.typeParameter.constraint.operator === ts.SyntaxKind.KeyOfKeyword) mappedNodes.push(node);
    if (ts.isIndexSignatureDeclaration(node) && node.parameters[0]?.type) keyTypeNodes.push(node.parameters[0].type);
    if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && !rooted.has(node.typeName.text))
      keyTypeNodes.push(...(node.typeArguments ?? []));
    node.forEachChild(findComputed);
  };
  if (!carriesContext) findComputed(source);
  if (importNodes.length || localNodes.length || globalNodes.length || globalValueNodes.length || importMetaNodes.length ||
      firstArray || firstAsync || keyNodes.length || ambientNames.length || staticNodes.length ||
      classTestNodes.length || classReadNodes.length || contextualNodes.length || assignNodes.length ||
      staticTypeNodes.length ||
      hookTestNodes.length || receiverNodes.length || enumNodes.length || computedNodes.length || symbolNameNodes.length ||
      keyTypeNodes.length || mappedNodes.length || bindingNodes.length || iterableNodes.length || spreadNodes.length ||
      restTargets.length || privateNodes.length || inKeyNodes.length || receiverTargetNodes.length || libraryNameNodes.length || elementReadNodes.length || lengthReadNodes.length || openReadNodes.length ||
      regexpNodes.length || dispatchNodes.length || blockNodes.length) {
    const first =importNodes[0] ?? localNodes[0] ?? globalNodes[0] ?? globalValueNodes[0] ?? importMetaNodes[0] ?? firstArray ??
      firstAsync ?? keyNodes[0] ?? ambientNames[0] ?? staticNodes[0] ?? classTestNodes[0] ?? classReadNodes[0] ?? contextualNodes[0] ?? assignNodes[0] ??
      hookTestNodes[0] ?? staticTypeNodes[0] ?? receiverNodes[0] ?? enumNodes[0] ??
      computedNodes[0] ?? symbolNameNodes[0] ?? keyTypeNodes[0] ?? bindingNodes[0] ?? iterableNodes[0] ??
      spreadNodes[0] ?? restTargets[0]?.node ?? privateNodes[0] ?? inKeyNodes[0] ?? receiverTargetNodes[0] ?? libraryNameNodes[0] ?? elementReadNodes[0] ?? lengthReadNodes[0] ?? openReadNodes[0] ??
      regexpNodes[0] ?? dispatchNodes[0] ?? blockNodes[0];
    if (!first) throw Error("missing declaration root");
    // Named, default and namespace imports. A type import joins the
    // declaration graph; a value import is an assumption at the type its
    // declaration states, a default import the module's `default` export's.
    // An import binding nothing runs the module for its effects alone.
    for (const node of importNodes) {
      const clause = node.importClause;
      if (!clause || (!clause.name && !clause.namedBindings))
        gate.fail(node, "an import binding no name is outside the source fragment");
    }
    // TypeScript resolves every name, in the project that owns the file or the
    // one named explicitly: the declaration graph is the compiler's.
    try {
      declarations = collectDeclarations(resolutionFile, { tsconfigPath, client: source,
        ...(diagnostic ? { diagnostic: (pos: Span, reason: string): void => {
          diagnostic.push({ pos, region: pos, reason,
            recovery: "opaque declaration contract; binding identities retained" });
        } } : {}),
        ...(family.given ? { familySelection: family.given } : {}),
        ...(family.selected ? { familySelected: family.selected } : {}),
        namespaceMembers: [...members.values()].map(m => ({ local: m.local, imported: m.imported,
          specifier: m.specifier, uses: m.uses.map(u => ({ span: gate.span(u.node), name: gate.span(u.name),
            value: u.value, callee: u.callee })) })),
        locals: localNodes.map(node => gate.span(node)),
        globals: globalNodes.map(node => gate.span(node)),
        globalValues: globalValueNodes.map(node => gate.span(node)),
        importMeta: importMetaNodes.map(node => gate.span(node)),
        ambient: ambientNames.map(node => gate.span(node)),
        root: gate.span(first),
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
        importedClassTest: ([start, end]) => gate.importedClassTests.add(`${start}:${end}`),
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
          // A function literal that is the whole initializer runs only after
          // the binding holds it: its reads are the recursive constant's self
          // entry (SOURCE-ELABORATION.md, "Recursive constants").
          let literal: Node | undefined = initializer;
          while (literal && ts.isParenthesizedExpression(literal)) literal = literal.expression;
          const selfEntry = !!literal && (ts.isArrowFunction(literal) || ts.isFunctionExpression(literal));
          const inInitializer = !selfEntry && !!initializer && start >= initializer.getStart(source) && end <= initializer.end;
          // A loop head's binding exists, uninitialized, while the head's
          // own expression runs: `for (const xs of xs)` throws there.
          const loop = declaration?.parent?.parent;
          const iterated = loop && (ts.isForOfStatement(loop) || ts.isForInStatement(loop)) ? loop.expression : undefined;
          const inHead = !!iterated && start >= iterated.getStart(source) && end <= iterated.end;
          // A one-name `let` or `const` of a block is an early binding
          // there, every mention a checked access (`markEarly`); a mention
          // above any other declaration is refused.
          const statement = declaration?.parent?.parent;
          const block = !!declaration && ts.isVariableDeclaration(declaration) && ts.isIdentifier(declaration.name) &&
            !!statement && ts.isVariableStatement(statement) && !!statement.parent && ts.isBlock(statement.parent);
          if (read && ((start < dStart && !block) || inInitializer || inHead)) early.push(read);
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
        libraryNames: libraryNameNodes.map(node => gate.span(node)),
        libraryName: ([start, end]) => gate.libraryNames.add(`${start}:${end}`),
        libraryValues: libraryValueNodes.map(node => gate.span(node)),
        libraryValue: ([start, end]) => gate.libraryValues.add(`${start}:${end}`),
        elementReads: elementReadNodes.map(node => gate.span(node)),
        lengthReads: lengthReadNodes.map(node => gate.span(node)),
        byteRead: ([start, end], intrinsic) => gate.byteReads.set(`${start}:${end}`, intrinsic),
        hostElement: ([start, end]) => gate.hostElements.add(`${start}:${end}`),
        openReads: openReadNodes.map(node => gate.span(node)),
        openRead: ([start, end], intrinsic) => gate.openReads.set(`${start}:${end}`, intrinsic),
        regexps: regexpNodes.map(node => gate.span(node)),
        regexp: ([start, end], intrinsic) => gate.regexps.set(`${start}:${end}`, intrinsic),
        dispatchCalls: dispatchNodes.map(node => gate.span(node)),
        dispatch: ([start, end], intrinsic) => gate.dispatches.set(`${start}:${end}`, intrinsic),
        restTargets: restTargets.map(({ node, index }) => ({ span: gate.span(node), index })),
        restSlice: ([start, end]) => gate.slices.add(`${start}:${end}`),
        computed: computedNodes.map(node => gate.span(node)),
        computedType: ([start, end], result) => gate.computedTypes.set(`${start}:${end}`, result),
        blockTypes: blockNodes.map(node => gate.span(node)),
        blockType: ([start, end], result) => gate.blockTypes.set(`${start}:${end}`, result),
        completion: ([start, end], result) => gate.completions.set(`${start}:${end}`, result),
        symbolNames: symbolNameNodes.map(node => gate.span(node)),
        keyTypes: keyTypeNodes.map(node => gate.span(node)),
        keyType: ([start, end], keys) => gate.keyTypes.set(`${start}:${end}`, keys),
        mappedTypes: mappedNodes.map(node => gate.span(node)),
        mappedType: ([start, end], members) => gate.mappedMembers.set(`${start}:${end}`, members),
        symbolName: ([start, end], result) => gate.symbolNames.set(`${start}:${end}`, result),
        globalTest: ([start, end]) => gate.globalTests.add(`${start}:${end}`),
        assertionCall: ([start, end]) => gate.assertionCalls.add(`${start}:${end}`),
        globalIntrinsic: ([start, end], name) => gate.globalIntrinsics.set(`${start}:${end}`, name),
        globalConstruct: ([start, end]) => gate.globalConstructs.add(`${start}:${end}`),
        enums: enumNodes.map(node => gate.span(node)),
        enumMember: ([start, end], value) => {
          for (const info of gate.enums.values())
            for (const m of info.members) if (m.span[0] === start && m.span[1] === end) m.value = value;
        },
        enumMemberRead: ([start, end], member) => gate.enumMemberReads.set(`${start}:${end}`, member.join(":")),
        importedEnum: (local, members, reverse) => gate.importedEnums.set(local, { members, reverse }),
        hostGuard: (local, entry, domain, field, tags) =>
          gate.hostGuards.set(local, { domain, field, tags, onUndefined: entry.onUndefined }),
        constEnumReads: constEnumNodes.map(node => gate.span(node)),
        constEnumRead: ([start, end], value) => gate.constEnumReads.set(`${start}:${end}`, value),
        library: ([start, end], library, local) => {
          const node = globalNodes.find(n => n.getStart(source) === start && n.end === end);
          if (node) gate.libraryTypes.set(node.text, library);
          // An imported type the overlay of library types states.
          else if (library.k === "stated" && importNodes.some(n => n.getStart(source) === start && n.end === end))
            gate.libraryTypes.set(local, library);
        },
        record: identity => gate.recordKeys.add(definitionKey(identity)),
        awaited: () => { gate.standardAwaited = true; },
        resolvable: () => { gate.standardResolvable = true; },
        awaitable: () => { gate.standardAwaitable = true; },
        within: () => { gate.standardWithin = true; },
        associatedAlias: (name, identity) => {
          const alias = aliasNodes.find(node => node.name.text === name &&
            node.getStart(source) === identity.span[0] && node.end === identity.span[1]);
          if (alias) gate.resolutionAliases.set(name, alias);
          else gate.fail(null, "an external associated-result alias requires retained symbol resolution");
        },
        ...(seen ? { seen } : {}) });
      gate.symbolIdentities = declarations.symbols;
    } catch (error) {
      const declared = declarationSpanOf(error);
      const at = declared
        ? [...importNodes, ...memberNodes, ...localNodes, ...globalNodes, ...globalValueNodes, ...importMetaNodes, ...(firstArray ? [firstArray] : []),
            ...(firstAsync ? [firstAsync] : []), ...keyNodes, ...ambientNames.map(topStatement), ...staticNodes,
            ...classTestNodes, ...classReadNodes, ...contextualNodes, ...assignNodes,
            ...receiverNodes, ...enumNodes, ...constEnumNodes, ...computedNodes, ...symbolNameNodes,
            ...keyTypeNodes, ...bindingNodes, ...privateNodes, ...blockNodes].find(node =>
            node.getStart(source) === declared[0] && node.end === declared[1]) ?? expressionAt(source, declared) ?? first
        : first;
      const failure = toolFailureOf(error);
      if (failure) gate.toolFailure(at, failure, error);
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
    gate.tagSymbols = new Set(declarations.symbols.flatMap((s, i) => isTagSymbol(s) ? [i] : []));
    for (const { declaration } of declarations.definitions)
      gate.typeIdentities.add(JSON.stringify([declaration.module, declaration.span, declaration.name]));
    gate.recordDefinitions = new Map(declarations.definitions.map(d => [definitionKey(d.declaration), d]));
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
        definition.parameters.filter(p => !p.defaulted).length,
        definition.parameters.length, identity, node,
        definition.expression ?? gate.fail(first, `a root without an equation: ${identity.module}#${identity.name}`));
    }
    // Every collected equation is available by identity, including block
    // aliases reached only through another alias's equation.
    for (const definition of declarations.definitions)
      if (definition.expression)
        gate.registerEquation(definition.declaration, definition.parameters.length, definition.expression);
  }
  // Carried context skips aliases its old fragment could not state. Every
  // retained declaration now has one source equation, shared with imports.
  // A function without a body is a declaration, not an example of one.
  const declared = carriesContext ? fnNodes.filter((s) => s.body) : fnNodes;
  // An imported module's function the gate refuses is absent, with the
  // reason; its other functions stay. Its code is not lowered, so the gate
  // refuses the module where any of its code, lowered or not, writes the
  // binding of one of its function declarations: an import reads that
  // binding as the declaration's closure.
  if (location !== null)
    for (const s of declared)
      if (s.name && writesName(source, s.name.text))
        gate.fail(s.name, `a module whose code writes the binding of its function ${s.name.text}`);
  const absent: ModuleAst["absent"] = [];
  const leftOut = (s: FunctionDeclaration, reason: string): void => {
    absent.push({ name: s.name?.text ?? "", namePos: s.name ? gate.span(s.name) : gate.span(s), reason });
  };
  let lowered = location === null ? declared.map((s) => ({ s, fn: gate.functionDecl(s) }))
    : declared.flatMap((s) => {
      try {
        return [{ s, fn: gate.functionDecl(s) }];
      } catch (error) {
        passToolFailure(error);
        leftOut(s, messageOf(error));
        return [];
      }
    });
  // A function left out is no binding of the module's run: a kept function
  // reading one is left out with it, until no kept function reads one.
  const absentNames = (): Set<string> => new Set(absent.flatMap((a) => a.name ? [a.name] : []));
  const local = (id: Identifier): string => gate.local(id);
  for (let changed = true; changed;) {
    const names = absentNames();
    const kept = lowered.filter(({ s }) => {
      const read = readOf(s, names, local);
      if (read) leftOut(s, gate.refusal(read, `a read of ${read.text}, a function of its module left out`));
      return !read;
    });
    changed = kept.length < lowered.length;
    lowered = kept;
  }
  const parsed = lowered.map(({ fn }) => fn);
  // Every enum's members must have values, whether or not it runs.
  for (const e of enumNodes) gate.enumMembers(e.name.text);
  const init = initNodes.flatMap((s) => ts.isClassDeclaration(s) ? [gate.classStmt(s)]
    : ts.isEnumDeclaration(s) ? gate.enumStmt(s) : [gate.stmt(s)]);
  // The module's top-level code runs as written: its read of a function left
  // out refuses the module.
  const leftNames = absentNames();
  for (const s of initNodes) {
    const read = readOf(s, leftNames, local);
    if (read) gate.fail(read, `the module's top-level code reads ${read.text}, a function of its module left out`);
  }
  if (location === null && parsed.length === 0 && init.length === 0) gate.fail(null, "no functions in file");
  // `%ThrowUninitialized%` was listed where a binding may be early, by
  // spelling (`earlyCandidate`); the file keeps it only where the lowering
  // marked one (`markEarly`), so the dependency is exact.
  if (gate.earlyDecls.size === 0)
    declarations = { ...declarations,
      values: declarations.values.filter(v => v.binding.local !== throwUninitializedName) };
  const sourceSha256 = createHash("sha256").update(text).digest("hex");
  // A module identity is its path from the project's root, the directory of
  // its tsconfig: where a file names its project, its imports resolve from
  // there, a snapshot's included.
  const root = tsconfigPath ? (tsconfigPath.endsWith(".json") ? dirname(resolve(tsconfigPath)) : resolve(tsconfigPath))
    : null;
  const importedFrom = importedModules(importNodes, checker, declarations.values, root);
  const ast: Ast = { file, sourceSha256, declarations, functions: parsed, init, modules: [] };
  const module: ModuleAst | null = location === null ? null : renamedModule({ location, sourceSha256,
    declarations, init, functions: parsed, absent }, absolute, location);
  // A mapped type over a named type read before the document was complete,
  // by a term the graph handed the gate, names no declaration.
  if (deferredInAst(ast) || (module !== null && deferredInModule(module)))
    gate.fail(null, "a mapped type's value names its key, over a named type read before its definitions were complete");
  return { ast, module, imported: importedFrom };
}

/** The program modules a file imports functions from: each named value
 * import TypeScript binds to a function declaration with a body in a source
 * file of the program, outside the standard library, the tool's own
 * declarations and installed packages, with the module identity the
 * declaration document gives it. */
function importedModules(importNodes: ImportDeclaration[], checker: Checker,
    values: Ast["declarations"]["values"], root: string | null): ImportedModule[] {
  // Each value import's local name: a named import's, and a default
  // import's, which binds the module's `default` export.
  const elements = importNodes.flatMap((node) => {
    const bindings = node.importClause?.namedBindings;
    const clause = node.importClause;
    const typeOnly = !!clause && clause.phaseModifier === ts.SyntaxKind.TypeKeyword;
    if (typeOnly || !clause) return [];
    const named = !bindings || !ts.isNamedImports(bindings) ? []
      : bindings.elements.filter((e) => !e.isTypeOnly).map((e) => e.name);
    return clause.name ? [clause.name, ...named] : named;
  });
  if (elements.length === 0) return [];
  const symbols = checker.getSymbolAtLocation(elements);
  return elements.flatMap((element, i) => {
    const value = values.find((v) => v.binding.local === element.text);
    if (!value || value.construct || value.typeParams.length > 0 || value.type.k !== "function") return [];
    const location = value.declaration.module;
    if (location.startsWith("typescript/lib/") || location.startsWith("tscert/")) return [];
    if (root !== null) {
      const absolute = resolve(root, location);
      return /\.[cm]?ts$/.test(absolute) && !/\.d\.[cm]?ts$/.test(absolute) && !absolute.split("/").includes("node_modules")
        ? [{ absolute, location }] : [];
    }
    const symbol = symbols[i];
    if (!symbol) return [];
    const target = symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
    const declaration = target.declarations[0]?.resolve();
    if (target.declarations.length !== 1 || !declaration || !ts.isFunctionDeclaration(declaration) ||
        !declaration.body) return [];
    const source = declaration.getSourceFile();
    if (source.isDeclarationFile || source.fileName.split("/").includes("node_modules")) return [];
    return [{ absolute: source.fileName, location }];
  });
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
    if (out) writeText(out, JSON.stringify(seen, null, 1) + "\n");
  }
}
