/** The declaration graph of one source file's types. TypeScript's checker,
 * under the file's configured project, decides which declaration every name
 * denotes: imports, reexports, package entries, `paths`, links and globals
 * resolve exactly as the compiler resolves them. This module turns each
 * declaration reached into a source equation, or refuses a form the fragment
 * cannot state; a refusal never drops a declaration. */
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { DiagnosticCategory, ElementFlags, SignatureKind, SymbolFlags, TypeFlags, TypePredicateKind, isTupleType, isTypeReference, isUnionType, type Checker, type Program, type Project, type Symbol as CompilerSymbol, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, ExportDeclaration, FunctionDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, SourceFile, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";
// declaration-types.mts declares the declaration document this module writes, which the Fragment carries and Lean's EquationLowering reads.
// type-term.mts is the one reading of TypeScript type syntax as a source type term, which every declaration body here is read with.
// computed-types.mts states a type TypeScript computes (`typeof`, `keyof`, `T[K]`, template literals) as the equivalent source term, or refuses it.
// array-prototype.mts holds the reviewed contracts of the built-in prototypes, the only members of `Array.prototype` and the primitive prototypes this reader admits.
// intrinsics.mts declares the intrinsics this reader lists among the client's values: the trusted steps async functions, loops, spreads and patterns lower to.
// library-globals.mts is the reviewed overlay of the standard library's globals, the only global values this reader admits, at the signatures it states.
import type { Span } from "./span.mts";
import { childrenOf, nameOf } from "./syntax.mts";
import { classInstance, computedAlias, computedForm, expandMapped, mapped, mapTypeParts, members, numericKey, oneTerm, optionalTerm, restPositions, restTerm, signature, signatures, statedResult, substitute,
  typeTerm, validateAnnotation, visitType, WITHIN_PLACE, type Mapped, type MappedMember, type TermScope } from "./type-term.mts";
import { arrayPrototype, interfaceOverlay, mergeMessage, mergeRefusal, overlay, primitiveKinds, primitivePrototype,
  primitivePrototypeName, collectionIteratorMark, nativeCollectionIterator, nativeCollectionIteratorDefinition, type OverlayEntry, splitSeparators, type OverlayLibrary, type PrimitiveKind } from "./array-prototype.mts";
import { intrinsics, intrinsicModule, resolutionIntrinsics, resolvableDeclaration, stableDefinition, iterateIteratorName, iterateRegExpStringName, iterateMapName, iterateSetName, iterateStringName,
  iterationIntrinsic, hasPropertyName, elementAtName, nonThenable, restFromIntrinsic, spreadName, enumIntrinsic, enumMembersTerm,
  literalTerm, assertionFailureName, type EnumMemberValue, type EnumReverse } from "./intrinsics.mts";
import { compareTags, familyTable, footprintReading, type FamilyArm, type FamilyDescription, type FamilyGraph, type FamilyTable, type FlatMember, type GuardEntry, type TagValue } from "./host-families.mts";
import { compilerApiFamily, brandedTypes, hostBrands, hostEnums, hostNodeBuilders, hostNodeList, hostTypeRoots, hostViews, isRequest, readsAsOptionalUnknown, requestReading } from "./compiler-api.mts";
import { activeFamilies, familyOfFile, familyOfGuard, guardOfExport, importedExport, installationPath, isHostFile, selectionGuard, tagEnumMatches, hostEnumObject } from "./family-activation.mts";
import { errorInstance, globalEntry, globalOrigins, globalsOverlay, type GlobalEntry, type Stated } from "./library-globals.mts";
import { moduleEntries, reviewedText, type ModuleEntry } from "./library-modules.mts";
import { literalParts, regexpShape } from "./regexp-shape.mts";
import { dispatchIntrinsic, dispatchName, isDispatchMethod, libraryRegExpTerm, marks, nativeIterator, nativeIteratorDefinition,
  nativeRegExp, regexpIntrinsicName, reviewedRegExpMembers,
  type RegExpKeys } from "./regexp.mts";
import { computedType, enclosingBinders, inferredTerm, isInstanceReference, literalUnion, type ComputedContext } from "./computed-types.mts";
import type { DeclarationIdentity, DeclarationDocument, PropertyKey, Reference, TypeDefinition, TypeRoot, TypeTerm, ValueRoot, WrittenApplication } from "./declaration-types.mts";
import { literal, SweepError, writtenApplications, type Entity } from "./written-applications.mts";
import { makeProbe, type MergedParameter, type ProbeProgram } from "./type-probe.mts";
import { emptyEffect, ordinaryEffect, promiseEffect, type CallEffect } from "./type-graph.mts";
import { messageOf, passToolFailure, toolFailureOf } from "./thrown.mts";
// named-record.mts reads a named type's record shape, at which a mapped type read before its definition is expanded.
import { definitionKey, deferredIn, settleDocument } from "./named-record.mts";
// files.mts makes every file-system failure a tool failure.
import { orAbsent, readText, realPath, remembered, type Remembered } from "./files.mts";
// compiler-channel.mts opens and releases the compiler, every request's failure a tool failure.
import { openFrontEndCompiler, releaseCompiler } from "./compiler-channel.mts";
// declaration-session.mts retains a named project's compiler between collections.
import { inDeclarationSession, noteAutomaticCollection } from "./declaration-session.mts";

type TypeDeclaration = TypeAliasDeclaration | InterfaceDeclaration | ClassDeclaration;
const isTypeDeclaration = (node: Node): node is TypeDeclaration =>
  ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node) || ts.isClassDeclaration(node);

/** Whether `file` is a declaration of the compiler API's installation, the
 * one where the compiler-API contract's tables by name (its branded strings,
 * enums, node list and type roots) apply; another family's installation is
 * read by its own description alone. */
const compilerApiFile = (file: string): boolean => familyOfFile(file)?.marker === compilerApiFamily.marker;

/** Whether TypeScript's type is the compiler API's `NodeArray<T>`, which the
 * model reads as a dense readonly array of its elements (COMPILER-API.md,
 * "Node lists in the model"): iterated, spread and indexed as that array. */
const nodeListType = (type: Type): boolean => {
  const symbol = type.getSymbol();
  return symbol?.name === hostNodeList && !!symbol.declarations.length &&
    symbol.declarations.every(d => compilerApiFile(d.resolve()?.getSourceFile().fileName ?? ""));
};

/** A refusal located at a root of the client: an import declaration or one of
 * its own type declarations. One made of a caught error carries it as its
 * `cause`, so a tool failure stays one (`toolFailureOf`), located. */
export class DeclarationError extends Error {
  readonly at: Span;
  constructor(at: Span, message: string, cause?: unknown) {
    super(message, cause === undefined ? undefined : { cause });
    this.at = at;
  }
}

/** A caught error as the refusal of a declaration read at `span`. A tool
 * failure is no refusal: it is thrown on, located at `span`. */
const refusalAt = (span: Span, thrown: unknown): string => {
  if (toolFailureOf(thrown)) throw new DeclarationError(span, messageOf(thrown), thrown);
  return messageOf(thrown);
};

/** A TypeScript error as the gate read it: the file TypeScript names, whether
 * that is the client, and the span, as offsets and as 0-based line and
 * character. The text is TypeScript's own. */
export interface SeenDiagnostic {
  file: string;
  client: boolean;
  pos: Span;
  start: { line: number; character: number };
  end: { line: number; character: number };
  text: string;
}

/** A standard library type whose declaration is not what it means to
 * TypeScript, so a reference to it is read as that meaning (SOURCE-CONTRACTS.md,
 * "Library types"): `Array<T>` and `ReadonlyArray<T>` are the array types
 * `T[]` and `readonly T[]`, and a library type alias whose equation is a
 * mapped type, such as `Record<K, V>`, is that mapped type at the
 * reference's arguments. */
export type LibraryType =
  /** `dense`: the host package's node list, which has no hole. */
  | { k: "array"; readonly: boolean; dense?: true }
  | { k: "mapped"; parameters: number; template: Mapped };

/** A reference to `library` at `args`, located at `span`. */
export function libraryTerm(library: LibraryType, args: readonly TypeTerm[], span: Span,
    fail: (message: string) => never, record?: TermScope["record"]): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  if (library.k === "array") {
    const [element] = args;
    if (!element || args.length !== 1) return fail("an array type takes one type argument");
    return { k: "array", presence: library.dense ? "dense" : "readable", readonly: library.readonly, element, span };
  }
  if (args.length !== library.parameters) return fail("a mapped library type needs all its type arguments");
  const t = library.template;
  return expandMapped({ ...t, key: substitute(t.key, args), value: substitute(t.value, args),
    ...(t.identity ? { identity: { ...t.identity, object: substitute(t.identity.object, args) } } : {}) }, span, fail, record);
}

type FunctionTerm = Extract<TypeTerm, { k: "function" }>;

/** The arguments of a reference to `library`: at a mapped type's key
 * parameter, the keys `keys` computes where it can (an alias of literals is
 * its literals), otherwise each argument as `read` reads it. */
export function libraryArguments(library: LibraryType, nodes: readonly TypeNode[], read: (node: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm>,
    keys?: (node: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm | null>): Within<{ value: "any"; store: "grow" }, TypeTerm[]> {
  const named: number[] = [];
  const mentions = (t: TypeTerm): void => {
    if (t.k === "parameter") named.push(t.index);
    else if (t.k === "union") t.parts.forEach(mentions);
  };
  if (library.k === "mapped") mentions(library.template.key);
  return nodes.map((node, i) => (named.includes(i) ? keys?.(node) : null) ?? read(node));
}


/** The configured project named on a command line: a tsconfig file, or the
 * directory holding one. */
export function tsconfigOf(path: string): string {
  const absolute = resolve(path);
  return absolute.endsWith(".json") ? absolute : join(absolute, "tsconfig.json");
}

/** Open `file` in its configured TypeScript project, which must be strict:
 * `tsconfigPath` when given, read in a declaration session
 * (`declaration-session.mts`), otherwise the project that owns the file, in
 * a compiler of its own. The compiler reads the files on disk; only a probe
 * program (`type-probe.mts`) reads some of them with text of its own, in a
 * snapshot of its own. */
function withProject<T>(file: string, tsconfigPath: string | undefined,
  use: (checker: Checker, client: SourceFile, root: string, program: Program, probe: ProbeProgram) => T): T {
  if (tsconfigPath === undefined) return withOwnProject(file, use);
  // A named project is opened alone: opening the file as well would load
  // the project the compiler finds for it besides the named one.
  return inDeclarationSession(file, tsconfigPath, (project, probe) => useProject(file, project, () => {}, use, probe));
}

/** `use` over `project` as loaded for `file`: a strict configured project
 * holding the file whose own program has no error, `check`ed further. */
function useProject<T>(file: string, project: Project | undefined, check: (project: Project) => void,
  use: (checker: Checker, client: SourceFile, root: string, program: Program, probe: ProbeProgram) => T,
  probe: ProbeProgram): T {
  if (!project?.configFileName || !project.compilerOptions.strict)
    throw new DeclarationError([0, 0], `TypeScript did not load a strict tsconfig for ${file}`);
  check(project);
  const client = project.program.getSourceFile(file);
  if (!client) throw new DeclarationError([0, 0], `TypeScript did not load ${file}`);
  // The project itself must load: a type package it names, such as
  // `types: ["node"]`, that is not installed leaves its globals undeclared.
  const broken = project.program.getProgramDiagnostics().find(d => d.category === DiagnosticCategory.Error);
  if (broken) throw new DeclarationError([0, 0], `TypeScript reports an error in the project: ${broken.text}`);
  return use(project.checker, client, dirname(project.configFileName), project.program, probe);
}

/** `withProject` for the project the compiler finds for `file`, in a
 * compiler opened for it and released after it. */
function withOwnProject<T>(file: string,
  use: (checker: Checker, client: SourceFile, root: string, program: Program, probe: ProbeProgram) => T): T {
  noteAutomaticCollection();
  const overlay = new Map<string, string>();
  const api = openFrontEndCompiler(dirname(file), overlay);
  // The files the last probe replaced, read from disk again by the next. The
  // compiler keeps an open file's text over its changes: the client, open
  // for the graph's program, is closed for the probes'.
  let replaced: string[] = [];
  let opened = true;
  let config = "";
  // A probe's snapshot is released when the next one is made: the next
  // takes its unchanged files over from it.
  let previous: { dispose(): void } | null = null;
  const probe: ProbeProgram = (files, read) => {
    overlay.clear();
    for (const [name, text] of files) overlay.set(name, text);
    const snapshot = api.updateSnapshot({ ...(opened ? { closeFiles: [file] } : {}),
      openProjects: [config],
      fileChanges: { changed: [...new Set([...replaced, ...files.keys()])] } });
    opened = false;
    replaced = [...files.keys()];
    previous?.dispose();
    previous = snapshot;
    const project = snapshot.getProject(config);
    if (!project) throw Error("TypeScript did not load the probe program");
    return read(project.program, project.checker);
  };
  let thrown: { error: unknown } | null = null;
  try {
    const snapshot = api.updateSnapshot({ openFiles: [file] });
    return useProject(file, snapshot.getDefaultProjectForFile(file), (project) => {
      config = project.configFileName;
    }, use, probe);
  } catch (error) {
    thrown = { error };
    throw error;
  } finally {
    releaseCompiler(api, thrown);
  }
}

/** Whether a part of the declaration document names an array or a tuple
 * type, which Lean reads at `ArrayProto`. */
function namesArray(value: unknown): boolean {
  if (Array.isArray(value)) return value.some(namesArray);
  if (typeof value !== "object" || value === null) return false;
  if ("k" in value && (value.k === "array" || value.k === "tuple")) return true;
  return Object.values(value).some(namesArray);
}

/** A module's identity: the client by its absolute path, a standard library
 * file by name, anything else by its real path relative to the project. */
function moduleIds(clientFile: string, root: string, program: Program):
    { idOf: (file: SourceFile) => string; libraryFile: (file: SourceFile) => boolean } {
  const client = realPath(clientFile);
  const projectRoot = realPath(root);
  // The standard library is the files the compiler's own library resolution
  // gives the program (`isSourceFileDefaultLibrary`), whatever else is
  // named like one; only names of that form are asked. Every library
  // decision reads this membership.
  const libraries = new Set(program.getSourceFileNames().filter(name => /^lib\..*\.d\.ts$/.test(basename(name)))
    .flatMap(name => {
      const file = program.getSourceFile(name);
      return file && program.isSourceFileDefaultLibrary(file) ? [realPath(name)] : [];
    }));
  const libraryFile = (file: SourceFile): boolean => libraries.has(realPath(file.fileName));
  // The identities are disjoint by construction: the client by its absolute
  // path, a library file `typescript/lib/<file>`, any other file its path
  // from the project root, written `./…` inside it and `../…` outside, so
  // no other file's identity reads as a library file's.
  const idOf = (file: SourceFile): string => {
    const path = realPath(file.fileName);
    if (path === client) return clientFile;
    if (libraries.has(path)) return `typescript/lib/${basename(path)}`;
    const inside = relative(projectRoot, path).split(sep).join("/");
    return inside.startsWith("../") ? inside : `./${inside}`;
  };
  return { idOf, libraryFile };
}

/** What TypeScript binds `identifier` to, following import and export aliases. */
function targetOf(checker: Checker, identifier: Identifier): CompilerSymbol | null {
  const symbol = checker.getSymbolAtLocation(identifier);
  if (!symbol) return null;
  // getAliasedSymbol requires an alias: calling it on a symbol that already
  // denotes its declaration panics in tsgo.
  const target = symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
  // An unbound name yields either the unknown symbol or one with no declaration.
  return checker.isUnknownSymbol(target) || target.declarations.length === 0 ? null : target;
}

/** The import and export statements TypeScript passes through when it binds
 * `identifier`: each step of its alias chain, and, because an `export *` is
 * not an alias step, every star export of each module those statements name. */
function statementsOnPath(checker: Checker, identifier: Identifier):
  (ImportDeclaration | ExportDeclaration)[] {
  const out: (ImportDeclaration | ExportDeclaration)[] = [];
  const modules = new Set<string>();
  const starExports = (specifier: Node): void => {
    const module = checker.getSymbolAtLocation(specifier)?.declarations[0]?.resolve();
    if (!module || !ts.isSourceFile(module) || modules.has(module.fileName)) return;
    modules.add(module.fileName);
    for (const statement of module.statements)
      if (ts.isExportDeclaration(statement) && statement.moduleSpecifier && !statement.exportClause) {
        out.push(statement);
        starExports(statement.moduleSpecifier);
      }
  };
  let symbol = checker.getSymbolAtLocation(identifier);
  const seen = new Set<number>();
  while (symbol && symbol.flags & SymbolFlags.Alias && !seen.has(symbol.id)) {
    seen.add(symbol.id);
    let node: Node | undefined = symbol.declarations[0]?.resolve();
    while (node && !ts.isImportDeclaration(node) && !ts.isExportDeclaration(node) && !ts.isSourceFile(node))
      node = node.parent;
    if (node && (ts.isImportDeclaration(node) || ts.isExportDeclaration(node))) {
      out.push(node);
      if (node.moduleSpecifier) starExports(node.moduleSpecifier);
    }
    symbol = checker.getImmediateAliasedSymbol(symbol);
  }
  return out;
}

/** The expression at exactly `span`, the outermost one there. */
export function expressionAt(file: SourceFile, span: Span): Node | null {
  const visit = (node: Node): Node | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (node.getStart(file) === span[0] && node.end === span[1] && !ts.isSourceFile(node)) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The primitives among a type's values whose members a read reaches through
 * a wrapper's prototype. */
function primitivesOf(type: Type): PrimitiveKind[] {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  const flags: Record<PrimitiveKind, number> = { string: TypeFlags.StringLike, number: TypeFlags.NumberLike,
    bigint: TypeFlags.BigIntLike, boolean: TypeFlags.BooleanLike };
  return primitiveKinds.filter(kind => parts.some(part => part.flags & flags[kind]));
}

/** The identifier at exactly `span`, in TypeScript's tree of the client. */
function identifierAt(file: SourceFile, span: Span): Identifier | null {
  const visit = (node: Node): Identifier | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (ts.isIdentifier(node) && node.getStart(file) === span[0] && node.end === span[1]) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The outermost type node at exactly `span`. */
function typeNodeAt(file: SourceFile, span: Span): TypeNode | null {
  const visit = (node: Node): TypeNode | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (ts.isTypeNode(node) && node.getStart(file) === span[0] && node.end === span[1]) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The computed type (`computedForm`) at exactly `span`, or the application
 * of a computed alias (`computedAlias`) there. */
function computedAt(file: SourceFile, span: Span): TypeNode | null {
  const visit = (node: Node): TypeNode | null => {
    if (node.end < span[1] || node.pos > span[0]) return null;
    if (ts.isTypeNode(node) && (computedForm(node) !== null || ts.isTypeReferenceNode(node)) &&
        node.getStart(file) === span[0] && node.end === span[1]) return node;
    return node.forEachChild(visit) ?? null;
  };
  return visit(file);
}

/** The client's named imports: each must name exactly one declaration. */
/** A namespace member the parser found (`namespace-members.mts`): its
 * binding, the export it names, and its occurrences, each by the span of the
 * member read or qualified name and of the member's name. */
export type NamespaceMemberSpans = { local: string; imported: string; specifier: string;
  uses: { span: Span; name: Span; value: boolean; callee: boolean }[] };

/** What the gate reports for a node of the client: the answer TypeScript's
 * reading gives, or the reason it gives none. `ok` decides the arm. */
export type Answered<T> = { readonly ok: true; readonly value: T } | { readonly ok: false; readonly refused: string };

/** The type declared in a block a reference names (`blockTypes`): its
 * identity, its own parameters' count and how many have no default, and the
 * spellings of the enclosing type parameters it closes over, outermost
 * first, which come first among its definition's parameters. */
export type BlockType = { computed: boolean; declaration: DeclarationIdentity; required: number; total: number; captured: string[] };

/** The client's imports, each the binding `name` the client reads, the
 * identifier `at` TypeScript resolves to the export, and the span a refusal
 * names: a named import's specifier and its import declaration, a namespace
 * member's first occurrence (`members`). */
function importBindings(client: SourceFile, members: readonly NamespaceMemberSpans[]): { name: string; at: Identifier;
  imported: string; specifier: string; span: Span; typeOnly: boolean }[] {
  const named = client.statements.filter(ts.isImportDeclaration).flatMap(node => {
    const span: Span = [node.getStart(client), node.end];
    const clause = node.importClause;
    if (!clause || (!clause.name && !clause.namedBindings) || !ts.isStringLiteral(node.moduleSpecifier))
      throw new DeclarationError(span, "only named, default and namespace imports are resolved");
    const specifier = node.moduleSpecifier.text;
    const clauseTypeOnly = clause.phaseModifier === ts.SyntaxKind.TypeKeyword;
    // A default import binds the module's `default` export.
    const defaulted = clause.name ? [{ name: clause.name.text, at: clause.name, imported: "default", specifier, span,
      typeOnly: clauseTypeOnly }] : [];
    if (!clause.namedBindings || ts.isNamespaceImport(clause.namedBindings)) return defaulted;
    return [...defaulted, ...clause.namedBindings.elements.map(element => ({ name: element.name.text, at: element.name,
      imported: element.propertyName?.text ?? element.name.text, specifier, span,
      typeOnly: clauseTypeOnly || element.isTypeOnly }))];
  });
  const namespaced = members.map(member => {
    const [first] = member.uses;
    const at = first ? identifierAt(client, first.name) : null;
    if (!first || !at) throw new DeclarationError(first?.span ?? [0, 0], `TypeScript namespace member ${member.local} missing`);
    return { name: member.local, at, imported: member.imported, specifier: member.specifier, span: first.span,
      typeOnly: !member.uses.some(u => u.value) };
  });
  return [...named, ...namespaced];
}

/**
 * The declaration graph of `file`: one root per named import and per local
 * declaration at a span in `locals`, and every declaration reachable from them.
 * `client`, when given, is the parser's tree of the same file; TypeScript must
 * have read the same bytes, so the spans of both trees agree.
 */
export function collectDeclarations(file: string, options: {
  /** Diagnostic-only recovery; the caller must retain the enclosing diagnostic envelope. */
  diagnostic?: (pos: Span, reason: string) => void;
  tsconfigPath?: string;
  client?: SourceFile;
  /** The members the client reads through its namespace imports
   * (`namespace-members.mts`): each joins as a named import of its export
   * would, under its own binding; a call of one whose signatures state a
   * `this` parameter is refused at the call, since it passes the namespace
   * object as the receiver. */
  namespaceMembers?: readonly NamespaceMemberSpans[];
  locals?: readonly Span[];
  /** The client's type-reference names that are neither imported nor its own
   * declarations: each that TypeScript binds to a global declaration becomes
   * a root. A type parameter is not one. */
  globals?: readonly Span[];
  /** Told each of the client's global type names, at its first reference
   * (`globals`), that TypeScript binds to a library type read at its meaning
   * rather than joining the graph (`LibraryType`). */
  library?: (span: Span, library: LibraryType) => void;
  /** Told each definition that is a record written as one: an interface or
   * a type alias read as its declared body, outside a class and a host
   * type (`NamedRecords`, named-record.mts). */
  record?: (declaration: DeclarationIdentity) => void;
  /** The standard associated-result alias, resolved at a source name. */
  awaited?: (span: Span) => void;
  /** The verifier's resolution-qualification bound (`resolvable.d.ts`),
   * resolved at a source name. */
  resolvable?: (span: Span) => void;
  /** The verifier's observation-qualification bound (`resolvable.d.ts`),
   * resolved at a source name. */
  awaitable?: (span: Span) => void;
  /** The verifier's statement of a signature's effect, `Within`
   * (`resolvable.d.ts`), resolved at a source name. */
  within?: (span: Span) => void;
  /** A local alias whose complete body is expanded in the qualified scope. */
  associatedAlias?: (name: string, declaration: DeclarationIdentity) => void;
  /** The client uses arrays: `Array.prototype`'s contract joins the graph
   * (`array-prototype.mts`), at `arrays`, the first array the client writes. */
  arrays?: Span;
  /** A statement call of `node:assert/strict`'s `assert` or `ok` read as the
   * calculus's own test (`ModuleEntry.lowering`), by the call's span. */
  assertionCall?: (span: Span) => void;
  /** The first construct of the client that reaches the graph, where a
   * declaration merging into `Object` or `Function` is refused. */
  root?: Span;
  /** The overlay `Array.prototype` is read through; tests vary it. */
  arrayOverlay?: readonly OverlayEntry[];
  /** The client uses `async`, `await` or `for...of`: the intrinsics that
   * stand for them (`intrinsics.mts`) join its values, located at the first
   * such construct. */
  intrinsics?: { span: Span; names: string[] };
  /** The client's value references to names it neither imports nor binds:
   * each that TypeScript binds to a global variable, such as Node's
   * `process` or the standard library's `BigInt`, joins its values, read at
   * the members and call signatures those references select
   * (`selectGlobal`). The first reference locates it. */
  globalValues?: readonly Span[];
  /** Told each call of a global that the reviewed overlay reads as a test
   * of the calculus, such as `Array.isArray(e)`, by the call's span. */
  globalTest?: (span: Span, test: NonNullable<GlobalEntry["test"]>) => void;
  /** Told each call of a global that the reviewed overlay reads as a call of
   * an intrinsic, such as `Promise.resolve(v)`, by the call's span, with the
   * intrinsic's name; the intrinsics then join the values. */
  globalIntrinsic?: (span: Span, name: string) => void;
  /** Told each call of a global that the reviewed overlay reads as its
   * construct, such as `Error(m)`, by the call's span. */
  globalConstruct?: (span: Span) => void;
  /** The names the client's ambient declarations bind, `declare function f`,
   * `declare const x: T`, `declare class C`, one span per name (overloads
   * once): each joins its values at the type its declarations state. */
  ambient?: readonly Span[];
  /** The client's element keys that are identifiers, `e[k]`: each that
   * TypeScript binds to a `unique symbol` constant joins the symbols and is
   * reported to `symbolKey` with its index. */
  symbolKeys?: readonly Span[];
  symbolKey?: (span: Span, symbol: number) => void;
  /** The client's private names `#x` (a member's, or one a read, a write or
   * a call names): each joins the symbols as the key of the member that
   * declares it and is reported to `privateName` with its index. */
  privateNames?: readonly Span[];
  privateName?: (span: Span, symbol: number) => void;
  /** The client's member names of reads `X.y` with `X` an identifier: each
   * that TypeScript binds to a static member of a class the client declares
   * at its top level, `X` naming that class, is reported to `staticMember`
   * with the class's name. */
  staticReads?: readonly Span[];
  staticMember?: (span: Span, cls: string) => void;
  /** Those `X.m` reads whose static member is declared by a class `X`
   * extends, which `X` reaches through its prototype. */
  inheritedStatic?: (span: Span) => void;
  /** Identifiers spelling a class of the client by name: `instanceof` right
   * operands, and a class's own name in its body. */
  classTests?: readonly Span[];
  /** Called for each of them TypeScript binds to a class declared at the
   * client's top level, with the class's name. */
  classTest?: (span: Span, cls: string) => void;
  /** `instanceof` right operands naming other values: each whose type
   * TypeScript gives states `[Symbol.hasInstance]`, in a
   * declaration of the program, is reported to `hookTest`. */
  hookTests?: readonly Span[];
  hookTest?: (span: Span) => void;
  /** The iterables of the client's `for...of` loops: each that TypeScript
   * types as a string, a `Set`, a `Map` or a host collection iterator is
   * reported to `iterable` with the iteration intrinsic that steps it
   * (`iterationIntrinsic`), which then joins the values; one it types as an
   * object with a `[Symbol.iterator]` that is none of these nor an array,
   * with `client`, which runs the iterator protocol, or `client-unclosable`
   * where the iterator's type states no `return`. Any other is left to
   * `%Iterate%`. */
  iterables?: readonly Span[];
  /** Likewise the operands of the client's argument spreads, `f(...x)`: one
   * of these kinds is reported with its spread intrinsic (`spreadName`). */
  spreads?: readonly Span[];
  /** A program iterable is reported with the well-known `Symbol.iterator`'s index
   * among the symbols, which its protocol reads the iterator method by. */
  iterable?: (span: Span, intrinsic: string, iteratorSymbol: number | null) => void;
  /** The targets of the client's array pattern rests, each with the number of
   * positions before it: each TypeScript types as no one tuple of required
   * positions is a slice, reported to `restSlice`, and `%RestFrom:k%`
   * (`restFromIntrinsic`) joins the values. */
  restTargets?: readonly { span: Span; index: number }[];
  restSlice?: (span: Span) => void;
  /** The keys of the client's `k in o` tests: each TypeScript types as other
   * than string literals is reported to `hostIn`, and the intrinsics, among
   * them `%HasProperty%`, which answers such a test, join the values. */
  inKeys?: readonly Span[];
  hostIn?: (span: Span) => void;
  /** The member names `m` of the client's `o.m.call(…)`, `.apply` and
   * `.bind` targets: each TypeScript resolves to a method is reported to
   * `methodTarget`. */
  receiverTargets?: readonly Span[];
  methodTarget?: (span: Span) => void;
  /** Names the parser lowers specially where they are the standard
   * library's (`Object` of `Object.assign`, the member `call`, `apply` or
   * `bind` of a function): each TypeScript binds to declarations of the
   * standard library alone is reported to `libraryName`. */
  libraryNames?: readonly Span[];
  libraryName?: (span: Span) => void;
  /** Names the file declares nowhere: each TypeScript binds to the standard
   * library's `var` or function declarations alone, whose read runs no code
   * and cannot throw, is reported to `libraryValue`. */
  libraryValues?: readonly Span[];
  libraryValue?: (span: Span) => void;
  /** The client's element reads `e[k]`: each whose object TypeScript types
   * as arrays, tuples and node lists only and whose key as `number`, no literal, is
   * reported to `hostElement`, and the intrinsics, among them
   * `%ElementAt%`, which reads it, join the values. */
  elementReads?: readonly Span[];
  hostElement?: (span: Span) => void;
  /** The client's regular expression literals: each is reported to
   * `regexp` with the intrinsic it is a call of, `%RegExp:Σ%` for its shape
   * Σ (`regexp-shape.mts`), which joins the values at `() => N(Σ)`
   * (`regexp.mts`). */
  regexps?: readonly Span[];
  regexp?: (span: Span, intrinsic: string) => void;
  /** The client's calls `s.m(o, …)` of a `String.prototype` method that
   * dispatches to its argument (`dispatchMethods`): each whose receiver
   * TypeScript types as a string and whose first argument as an object is
   * reported to `dispatch` with `%Dispatch:m%`, which joins the values
   * (`dispatchIntrinsic`). */
  dispatchCalls?: readonly Span[];
  dispatch?: (span: Span, intrinsic: string) => void;
  /** Identifiers of the client that may name one of its local bindings: each
   * that TypeScript binds to a value declaration in the client is reported
   * to `bindingRead` with the span of that declaration's name. A shorthand
   * property `{ x }` names the binding its value reads. */
  bindingReads?: readonly Span[];
  bindingRead?: (span: Span, declaration: Span) => void;
  /** The names of the client's closure parameters written without a type:
   * each is reported to `contextualParam` with the type TypeScript gives it
   * from its context, as a type term (`contextualTerm`), or the reason none
   * states it. */
  /** The names of the client's static fields written without an
   * annotation: each is reported to `staticType` with the type TypeScript
   * gives it, as a term (`contextualTerm`), or why none. */
  staticTypes?: readonly Span[];
  staticType?: (span: Span, result: Answered<TypeTerm>) => void;
  contextualParams?: readonly Span[];
  contextualParam?: (span: Span, result: Answered<TypeTerm>) => void;
  /** The client's calls `Object.assign(arrow, literal)` written without type
   * arguments: each is reported to `assignTypes` with the two TypeScript
   * infers, the arrow's function type and the literal's record, as the
   * callable form's annotations, or the reason no term states them. */
  assignCalls?: readonly Span[];
  assignTypes?: (span: Span, result: Answered<{ functionType: TypeTerm; bagType: TypeTerm }>) => void;
  /** The client's top-level enum declarations: each must be one TypeScript
   * accepts, and each member, by its span, is reported to `enumMember` with
   * the value TypeScript computes for it, which is the value its emit writes
   * (SOURCE-CONTRACTS.md, "Enums"), or undefined where it computes none. */
  enums?: readonly Span[];
  enumMember?: (span: Span, value: string | number | undefined) => void;
  /** Told each imported enum's local name and members: the client's
   * annotations read its type and its members' literal types. */
  importedEnum?: (local: string, members: readonly EnumMemberValue[], reverse: EnumReverse) => void;
  /** Told each import binding of a listed guard of the compiler API's family
   * (HOST-FAMILIES.md, "Calls"): its local name, its entry, the domain its
   * declared parameter states, the field a node guard tests (the family's
   * tag), and the values of its tag set, the family's constants. */
  hostGuard?: (local: string, entry: GuardEntry, domain: TypeTerm, field: string | null,
    tags: readonly (number | string)[]) => void;
  /** An ambient enum (`declare enum`, not `const`) joins the values as the
   * environment's object, at its members' object type (`enumMembersTerm`).
   * An enum with a member TypeScript computes no value for joins the
   * intrinsic `%Enum:E%` that builds its object (`enumIntrinsic`), and each
   * read of one of its members in such a member's initializer, bare or
   * `E.M`, `E["M"]`, is reported to `enumMemberRead` with the member's span. */
  enumMemberRead?: (span: Span, member: Span) => void;
  /** The client's reads `X.y` and `X["y"]` with `X` an identifier: each that
   * TypeScript binds to a member of a `const enum` the client declares is
   * reported to `constEnumRead` with the member's value, which TypeScript
   * writes in place of the read. */
  constEnumReads?: readonly Span[];
  constEnumRead?: (span: Span, value: string | number) => void;
  /** The receivers of the client's member reads, `e.k` and `e[k]`: each
   * that TypeScript types as a string, number, bigint or boolean, or a union
   * holding one, reads that primitive's members through its wrapper's
   * prototype, whose contract (`array-prototype.mts`) then joins the graph
   * and whose built-in value joins the values, located at the first such
   * receiver. */
  memberReceivers?: readonly Span[];
  /** The client's computed types (`computedForm`) outside its type
  * declarations, each outermost one: each is evaluated
  * (`computed-types.mts`) and reported to `computedType` with its term, or
  * with the reason it has none. */
  computed?: readonly Span[];
  computedType?: (span: Span, result: Answered<TypeTerm>) => void;
  /** The client's type references spelling a name some type declared in
   * one of its blocks has: each TypeScript binds to such a declaration is
   * reported to `blockType` with that declaration, which joins the graph,
   * its own arity and the spellings of the type parameters it closes over,
   * each the binder TypeScript resolves at the reference; or with the
   * reason it is refused (SOURCE-CONTRACTS.md, "Block-scoped type
   * declarations"). */
  blockTypes?: readonly Span[];
  blockType?: (span: Span, result: Answered<BlockType>) => void;
  /** Told, for each client reference omitting arguments of a declaration,
   * the omitted arguments: each parameter's default at the arguments before
   * it, or the reason it has none. */
  completion?: (span: Span, result: Answered<TypeTerm[]>) => void;
  /** Type nodes of the client's annotations that may be a mapped type's keys:
   * each is reported to `keyType` with the union of literals and primitives
   * TypeScript computes for it, or null. */
  keyTypes?: readonly Span[];
  keyType?: (span: Span, keys: TypeTerm | null) => void;
  /** The client's mapped types over `keyof`: each is reported to
   * `mappedType` with its members as TypeScript resolves them, or null. */
  mappedTypes?: readonly Span[];
  mappedType?: (span: Span, members: readonly MappedMember[] | null) => void;
  /** The computed keys `[k]` and `[S.k]` of the client's annotations' type
   * literals: each that names a `unique symbol` constant or readonly property
   * joins the symbols and is reported to `symbolName` with its index, any
   * other with the reason it names none. */
  symbolNames?: readonly Span[];
  symbolName?: (span: Span, result: Answered<number | { literal: string; value: string | number }>) => void;
  /** Told each TypeScript error the gate reads while deciding whether a
   * declaration is clean, whether or not it refuses the source: every error
   * TypeScript reports in each file it examines, each once. */
  seen?: (diagnostic: SeenDiagnostic) => void;
  /** The run's tag selection of a host family, by its marker
   * (HOST-FAMILIES.md, "Residuals"), when an imported module of the run is
   * lowered: the one read of the selection, made by family; otherwise it is
   * computed over the modules the checked file reaches and reported to
   * `familySelected`. */
  familySelection?: (marker: string) => readonly TagValue[] | undefined;
  familySelected?: (selection: ReadonlyMap<string, readonly TagValue[]>) => void;
} = {}): DeclarationDocument {
  const recover = (pos: Span, error: unknown): void => {
    if (!options.diagnostic) {
      if (error instanceof DeclarationError) throw error;
      throw new DeclarationError(pos, messageOf(error), error);
    }
    passToolFailure(error);
    options.diagnostic(error instanceof DeclarationError ? error.at : pos, messageOf(error));
  };
  const clientFile = resolve(file);
  return withProject(clientFile, options.tsconfigPath, (checker, client, root, program, probeProgram) => {
    if (options.client && options.client.getFullText() !== client.getFullText())
      throw new DeclarationError([0, 0], "TypeScript client source bytes differ");
    const { idOf, libraryFile } = moduleIds(clientFile, root, program);
    // A module of the program: a source file outside the standard library,
    // the host packages and any installed package.
    const programFile = (file: SourceFile): boolean => !file.isDeclarationFile && !libraryFile(file) &&
      !isHostFile(file.fileName) && !file.fileName.split(sep).includes("node_modules");
    // The verifier's declaration file (`resolvable.d.ts`): the repository's,
    // or a file of exactly its bytes, which declares the same aliases (the
    // census's copy of tools/ holds one).
    let verifierText: string | null = null;
    const verifierFile = (file: SourceFile): boolean => {
      if (file.fileName === resolvableDeclaration) return true;
      verifierText ??= readText(resolvableDeclaration);
      return file.text === verifierText;
    };
    // Statements (`Within<F, T>`, SOURCE-ELABORATION.md, "Stated effects"):
    // a reference to the verifier's `Within`, by the declaration TypeScript
    // binds it to. A statement is the program's own: one written outside the
    // program's sources, or in an ambient declaration, states an effect of
    // code no run checks, and so does one reached while an external value's
    // type is read (`externalReads`). The definitions whose equations read
    // one are recorded, so that an external value's type reaching one is
    // refused (`externalStatements`).
    const verifierAlias = (identifier: Identifier): string | null => {
      const declaration = targetOf(checker, identifier)?.declarations[0]?.resolve();
      return declaration && ts.isTypeAliasDeclaration(declaration) &&
        verifierFile(declaration.getSourceFile()) ? declaration.name.text : null;
    };
    const ambient = (node: Node): boolean => {
      for (let at: Node | undefined = node; at; at = at.parent)
        if (at.flags & ts.NodeFlags.Ambient) return true;
      return false;
    };
    let externalReads = 0;
    const statedDefinitions = new Set<string>();
    const programClasses = new Set<string>();
    // The definition whose equation is being read (`collect`): a statement
    // read meanwhile, through a computed type its equation names included,
    // is its.
    let collecting: string | null = null;
    const statement = (reference: ts.TypeReferenceNode, owner: string | null): boolean => {
      if (!ts.isIdentifier(reference.typeName) || verifierAlias(reference.typeName) !== "Within") return false;
      if (!programFile(reference.getSourceFile()) || ambient(reference))
        throw Error("`Within` outside the program's sources, or in an ambient declaration, states an effect of code no run checks");
      if (externalReads > 0)
        throw Error("a value declared outside the program's sources is typed by a statement (`Within`), an effect of code no run checks");
      const at = owner ?? collecting;
      if (at !== null) statedDefinitions.add(at);
      return true;
    };
    // A read of a host class's member its named view does not list is
    // refused where it is written, naming the view (COMPILER-API.md, reading
    // rule 4, L6).
    const outsideViews = (node: Node): void => {
      if (ts.isPropertyAccessExpression(node) && ts.isIdentifier(node.name)) {
        const declarations = (checker.getTypeAtLocation(node.expression)?.getSymbol()?.declarations ?? [])
          .map(d => d.resolve()).filter((d): d is TypeDeclaration => !!d && isTypeDeclaration(d));
        for (const d of declarations) {
          if (!(ts.isClassDeclaration(d) || ts.isInterfaceDeclaration(d)) || !compilerApiFile(d.getSourceFile().fileName)) continue;
          const owner = d.name?.text ?? "";
          const view = hostViews.find(v => v.owner === owner);
          if (!view && !ts.isClassDeclaration(d)) continue;
          if (!(view?.members ?? []).some(m => m.name === node.name.text))
            // At the read's receiver, which the gate locates (`memberReceivers`).
            recover([node.expression.getStart(client), node.expression.end], Error(
              `${owner}.${node.name.text} is outside the named view ${owner} of the compiler-API contract (compiler-api.mts, reading rule 4)`));
        }
      }
      node.forEachChild(outsideViews);
    };
    outsideViews(client);
    // Everything the graph uses must be code TypeScript accepts: an error in a
    // used declaration or on the resolution path refuses it. Errors elsewhere in
    // those files, and in the client's function bodies, are not the graph's.
    const errors = new Map<string, readonly { pos: number; end: number; text: string }[]>();
    const clean = (node: Node, what: string): void => {
      const file = node.getSourceFile();
      let found = errors.get(file.fileName);
      if (!found) {
        found = [...program.getSyntacticDiagnostics(file.fileName),
          ...program.getSemanticDiagnostics(file.fileName)]
          .filter(d => d.category === DiagnosticCategory.Error && !untypedAmbientField(file, d));
        errors.set(file.fileName, found);
        for (const d of found)
          options.seen?.({ file: file.fileName, client: file === client, pos: [d.pos, d.end],
            start: file.getLineAndCharacterOfPosition(d.pos),
            end: file.getLineAndCharacterOfPosition(d.end), text: d.text });
      }
      const start = node.getStart(file);
      const error = found.find(d => d.pos < node.end && d.end > start);
      if (error) throw Error(`TypeScript reports an error in ${what}: ${error.text}`);
    };
    // The host's branded strings met (reading rule 5), by identity.
    const brands = new Set<string>();
    const brandKey = (id: DeclarationIdentity): string => `${id.module}#${id.name}#${id.span.join(":")}`;
    const identityOf = (node: TypeDeclaration): DeclarationIdentity => {
      const source = node.getSourceFile();
      // An anonymous class is refused where it is reached, so every
      // declaration here has a name.
      const identity: DeclarationIdentity = { module: idOf(source), name: node.name?.text ?? "",
        span: [node.getStart(source), node.end] };
      const brand = ts.isTypeAliasDeclaration(node) && compilerApiFile(source.fileName)
        ? brandedTypes.find(b => b.name === node.name.text) : undefined;
      if (brand) {
        if (node.getText(source).trim() !== brand.text)
          throw Error(`the branded string ${brand.name} is not declared as reviewed: ${brand.text}`);
        brands.add(brandKey(identity));
      }
      return identity;
    };
    const isBrand = (id: DeclarationIdentity): boolean => brands.has(brandKey(id));
    // The one declaration TypeScript binds a name to, with no error on it or
    // on the path to it.
    const resolveDeclarations = (identifier: Identifier, what: string): Node[] => {
      const target = targetOf(checker, identifier);
      if (!target) throw Error(`unresolved type reference ${what}`);
      const nodes = target.declarations.map((d): Node => {
        const node = d.resolve();
        if (!node) throw Error(`unresolved type reference ${what}`);
        return node;
      });
      // The verifier's `Within` and `Footprint` are no types: a statement
      // is read at a signature's result (`statedResult`), and nowhere else.
      if (nodes.some(n => ts.isTypeAliasDeclaration(n) && verifierFile(n.getSourceFile()) &&
          (n.name.text === "Within" || n.name.text === "Footprint")))
        throw Error(`${WITHIN_PLACE}: ${what}`);
      for (const statement of statementsOnPath(checker, identifier))
        clean(statement, `${idOf(statement.getSourceFile())} on the path to ${what}`);
      return nodes;
    };
    // Whether a declaration is a host type (COMPILER-API.md, reading rule
    // 1): a class of a host package, or an interface of it that is one of
    // its type roots or reaches one through `extends`: the compiler API's
    // `hostTypeRoots`, another family's root.
    const hostTypes = new Map<Node, boolean>();
    const hostType = (node: TypeDeclaration): boolean => {
      const known = hostTypes.get(node);
      if (known !== undefined) return known;
      hostTypes.set(node, false);
      let result = false;
      const description = familyOfFile(node.getSourceFile().fileName);
      if (description) {
        const roots = description.marker === compilerApiFamily.marker ? hostTypeRoots : [description.root.name];
        if (ts.isClassDeclaration(node)) result = true;
        else if (ts.isInterfaceDeclaration(node))
          result = roots.includes(node.name.text) || (node.heritageClauses ?? []).some(clause =>
            clause.types.some(base => ts.isIdentifier(base.expression) &&
              (targetOf(checker, base.expression)?.declarations ?? []).some(d => {
                const target = d.resolve();
                return !!target && isTypeDeclaration(target) && hostType(target);
              })));
      }
      hostTypes.set(node, result);
      return result;
    };
    // The name a type reference reads: an identifier, or the member of a
    // namespace import a qualified name `ns.T` reads, which TypeScript binds
    // to the export it names (`namespace-members.mts`); null for any other
    // qualified name.
    const memberName = (name: ts.EntityName): Identifier | null => {
      if (ts.isIdentifier(name)) return name;
      if (!ts.isIdentifier(name.left)) return null;
      const declaration = checker.getSymbolAtLocation(name.left)?.declarations[0]?.resolve();
      return declaration && ts.isNamespaceImport(declaration) ? name.right : null;
    };
    // The enum a name denotes, every declaration TypeScript binds it to an
    // enum's (merged enums are one), or null.
    const enumsOf = (identifier: Identifier): ts.EnumDeclaration[] | null => {
      const nodes = (targetOf(checker, identifier)?.declarations ?? []).map(d => d.resolve());
      const enums = nodes.filter((n): n is ts.EnumDeclaration => !!n && ts.isEnumDeclaration(n));
      return enums.length && enums.length === nodes.length ? enums : null;
    };
    // An enum's members, in order, each at the value TypeScript computes,
    // `undefined` where it computes none. Each declaration's members are
    // read from the checker once: a reference to a member reads all of them.
    const enumMembers = new Map<ts.EnumDeclaration, readonly EnumMemberValue[]>();
    const enumMembersOf = (enums: readonly ts.EnumDeclaration[], what: string): EnumMemberValue[] =>
      enums.flatMap(e => {
        clean(e, what);
        const known = enumMembers.get(e);
        if (known) return known;
        const members = e.members.map(m => {
          if (!ts.isIdentifier(m.name) && !ts.isStringLiteral(m.name)) throw Error(`an enum member of ${what} needs a plain name`);
          const value = checker.getConstantValue(m);
          if (typeof value === "number" && !Number.isFinite(value))
            throw Error(`an enum member of ${what} that is NaN or infinite has no literal type`);
          return { name: m.name.text, value };
        });
        enumMembers.set(e, members);
        return members;
      });
    // Whether a host enum is read as a value: one the compiler-API contract
    // lists (`hostEnums`, T5), in its installation; or the tag enum a
    // family's description names, in that family's installation, whose
    // members are those of the runtime object the family's activated entry
    // point exports (`tagEnumMatches`); where the object itself is read,
    // `bound`, the import that reads it binds that object as Node resolves
    // it (`boundHostEnum`).
    const readableHostEnum = (enums: readonly ts.EnumDeclaration[], name: string, bound: boolean | null): boolean => {
      if (enums.every(e => compilerApiFile(e.getSourceFile().fileName)) && hostEnums.some(h => h.name === name)) return bound !== false;
      const [first] = enums;
      const description = first ? familyOfFile(first.getSourceFile().fileName) : null;
      return !!description && description.tag.constants.enum === name && bound !== false &&
        enums.every(e => familyOfFile(e.getSourceFile().fileName) === description) &&
        tagEnumMatches(description, enumMembersOf(enums, name));
    };
    // Whether an enum's object holds its reverse mapping (SOURCE-CONTRACTS.md,
    // "Enums", `emitted-enum`): every declaration TypeScript merges is a
    // program module's, outside an ambient context, so TypeScript's emit
    // builds it; or the enum is a host enum whose runtime object is checked
    // to hold it (C1, `tagEnumMatches`). Any other enum's object is the
    // environment's, its members alone assumed.
    const enumReverse = (enums: readonly ts.EnumDeclaration[], name: string): EnumReverse => {
      if (enums.every(e => programFile(e.getSourceFile()) && !(e.flags & ts.NodeFlags.Ambient))) return "stated";
      return enums.every(e => isHostFile(e.getSourceFile().fileName)) && readableHostEnum(enums, name, null) ? "stated" : "none";
    };
    // The host families (HOST-FAMILIES.md): each active description's, read
    // through it by `familyTable`, from the declarations of the description's
    // installation as TypeScript resolves them. Each family's table is built
    // once, from the first declaration of its installation that reaches the
    // description's root.
    // The promises of the listed node guards the run reads, by their
    // families' markers and their definitions' names: each the tag values
    // of its entry.
    const guardPromises = new Map<string, Map<string, readonly TagValue[]>>();
    const baseDeclarations = (d: InterfaceDeclaration): InterfaceDeclaration[] =>
      (d.heritageClauses ?? []).flatMap(clause => clause.types.map(base => {
        if (!ts.isIdentifier(base.expression) || base.typeArguments?.length)
          throw Error(`the family ${familyOfFile(d.getSourceFile().fileName)?.marker ?? ""} reads no base ${base.getText(d.getSourceFile())} of ${d.name.text}`);
        const targets = (targetOf(checker, base.expression)?.declarations ?? []).map(x => x.resolve());
        const [only] = targets;
        if (!only || targets.length !== 1 || !ts.isInterfaceDeclaration(only))
          throw Error(`the base ${base.expression.text} of ${d.name.text} is not one interface`);
        return only;
      }));
    const isFamilyRoot = (d: InterfaceDeclaration): boolean => {
      const description = familyOfFile(d.getSourceFile().fileName);
      return !!description && d.name.text === description.root.name &&
        d.getText(d.getSourceFile()).split("\n")[0]?.trim() === description.root.text;
    };
    const rootOf = (d: InterfaceDeclaration, seen = new Set<InterfaceDeclaration>()): InterfaceDeclaration | null => {
      if (seen.has(d)) return null;
      seen.add(d);
      if (isFamilyRoot(d)) return d;
      for (const b of baseDeclarations(d)) {
        const r = rootOf(b, seen);
        if (r) return r;
      }
      return null;
    };
    type Family = { table: FamilyTable; members: Set<InterfaceDeclaration>; enums: readonly ts.EnumDeclaration[];
      literals: (type: TypeNode) => readonly TagValue[] | null; constants: readonly EnumMemberValue[] };
    const families = new Map<FamilyDescription, Family>();
    // A family's files: the root's and those its module statements name,
    // transitively, within its installation.
    const familyFiles = (root: InterfaceDeclaration, description: FamilyDescription): SourceFile[] => {
      const files: SourceFile[] = [];
      const visit = (file: SourceFile): void => {
        if (files.includes(file) || familyOfFile(file.fileName) !== description) return;
        files.push(file);
        for (const statement of file.statements)
          if ((ts.isImportDeclaration(statement) || ts.isExportDeclaration(statement)) && statement.moduleSpecifier) {
            const module = checker.getSymbolAtLocation(statement.moduleSpecifier)?.declarations[0]?.resolve();
            if (module && ts.isSourceFile(module)) visit(module);
          }
      };
      visit(root.getSourceFile());
      return files;
    };
    const familyFrom = (start: InterfaceDeclaration): Family | null => {
      const familyDescription = familyOfFile(start.getSourceFile().fileName);
      if (!familyDescription) return null;
      const known = families.get(familyDescription);
      if (known) return known.members.has(start) ? known : null;
      const root = rootOf(start);
      if (!root) return null;
      const reachesRoot = new Map<InterfaceDeclaration, boolean>();
      const reaching = (d: InterfaceDeclaration): boolean => {
        const known = reachesRoot.get(d);
        if (known !== undefined) return known;
        reachesRoot.set(d, false);
        // Through every base TypeScript binds to an interface, whatever its form.
        const result = d === root || (d.heritageClauses ?? []).some(clause => clause.types.some(base =>
          ts.isIdentifier(base.expression) && (targetOf(checker, base.expression)?.declarations ?? [])
            .some(x => { const t = x.resolve(); return !!t && ts.isInterfaceDeclaration(t) && reaching(t); })));
        reachesRoot.set(d, result);
        return result;
      };
      const interfaces = familyFiles(root, familyDescription).flatMap(file => file.statements.filter(ts.isInterfaceDeclaration))
        .filter(reaching);
      const tagType = root.members.find(m => nameOf(m)?.getText(root.getSourceFile()) === familyDescription.tag.field);
      const tagName = tagType && ts.isPropertySignatureDeclaration(tagType) && tagType.type &&
        ts.isTypeReferenceNode(tagType.type) && ts.isIdentifier(tagType.type.typeName) ? tagType.type.typeName : null;
      const enums = tagName && tagName.text === familyDescription.tag.constants.enum ? enumsOf(tagName) : null;
      if (!enums) throw Error(`the root ${root.name.text} states no ${familyDescription.tag.field} of the enum ${familyDescription.tag.constants.enum}`);
      const constants = enumMembersOf(enums, familyDescription.tag.constants.enum);
      // The tag values: the constants of the description's primitive.
      const primitive = familyDescription.tag.primitive;
      const values = [...new Set(constants.flatMap((c): TagValue[] => typeof c.value === primitive && c.value !== undefined ? [c.value] : []))]
        .sort(compareTags);
      // The tag values a type node states, through aliases of the package,
      // each alias followed once along the reading.
      const literalsAlong = (type: TypeNode, seen: Set<Node>): TagValue[] | null => {
        if (ts.isParenthesizedTypeNode(type)) return literalsAlong(type.type, seen);
        if (ts.isUnionTypeNode(type)) {
          const parts = type.types.map(t => literalsAlong(t, seen));
          return parts.every((p): p is TagValue[] => p !== null) ? [...new Set(parts.flat())].sort(compareTags) : null;
        }
        if (!ts.isTypeReferenceNode(type) || type.typeArguments?.length) return null;
        if (ts.isQualifiedName(type.typeName)) {
          const owner = memberName(type.typeName.left);
          const named = owner ? enumsOf(owner) : null;
          if (!named || !named.every(e => enums.includes(e))) return null;
          const member = type.typeName.right.text;
          const value = constants.find(c => c.name === member)?.value;
          return typeof value === primitive && value !== undefined ? [value] : null;
        }
        const target = (targetOf(checker, type.typeName)?.declarations ?? []).map(d => d.resolve());
        const [only] = target;
        if (!only || target.length !== 1 || seen.has(only)) return null;
        if (ts.isTypeAliasDeclaration(only) && !only.typeParameters?.length && isHostFile(only.getSourceFile().fileName)) {
          seen.add(only);
          return literalsAlong(only.type, seen);
        }
        return null;
      };
      // A type node's tag values, read once: the family's table and every
      // reading of its tags ask for the same nodes' values many times.
      const literalsRead = new Map<TypeNode, readonly TagValue[] | null>();
      const literals = (type: TypeNode): readonly TagValue[] | null => {
        if (literalsRead.has(type)) return literalsRead.get(type) ?? null;
        const values = literalsAlong(type, new Set());
        literalsRead.set(type, values);
        return values;
      };
      const graph: FamilyGraph = {
        interfaces,
        bases: baseDeclarations,
        literals,
        values,
        constantName: value => constants.find(c => c.value === value)?.name ?? String(value),
        tagParameter: d => {
          const own = d.members.find(m => nameOf(m)?.getText(d.getSourceFile()) === familyDescription.tag.field);
          const type = own && ts.isPropertySignatureDeclaration(own) ? own.type : undefined;
          const name = type && ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) ? type.typeName.text : null;
          return name !== null && (d.typeParameters ?? []).some(p => p.name.text === name) ? name : null;
        },
        questioned: m => (ts.isPropertySignatureDeclaration(m) || ts.isMethodSignatureDeclaration(m)) &&
          m.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
        name: m => { const n = nameOf(m); return n && ts.isIdentifier(n) ? n.text : null; },
        text: m => m.getText(m.getSourceFile()).trim(),
        mentions: (m, parameter) => {
          const visit = (n: Node): boolean => (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) &&
            n.typeName.text === parameter) || (n.forEachChild(visit) ?? false);
          return visit(m);
        },
        fail: message => { throw Error(`the family ${familyDescription.marker}: ${message}`); },
      };
      const family: Family = { table: familyTable(familyDescription, graph), members: new Set(interfaces), enums, literals, constants };
      families.set(familyDescription, family);
      return family.members.has(start) ? family : null;
    };
    // The constants of the family a listed guard's parameter states: those
    // of the family its member type belongs to, or of the tag enum itself,
    // as the entry's domain names it.
    const guardConstants = (declaration: FunctionDeclaration, entry: GuardEntry): readonly EnumMemberValue[] => {
      // The declaration, its parameter's family and the runtime guard are of
      // one description.
      const familyDescription = familyOfGuard(entry);
      if (familyOfFile(declaration.getSourceFile().fileName) !== familyDescription)
        throw Error(`the guard ${entry.name} is declared outside the installation of its family ${familyDescription.marker}`);
      const type = declaration.parameters[0]?.type;
      const name = type && ts.isTypeReferenceNode(type) && !type.typeArguments?.length ? memberName(type.typeName) : null;
      if (!name || name.text !== entry.domain)
        throw Error(`the guard ${entry.name} takes a parameter its entry's domain ${entry.domain} does not name`);
      if (entry.kind === "tag") {
        const enums = enumsOf(name);
        if (!enums || name.text !== familyDescription.tag.constants.enum ||
            !enums.every(e => familyOfFile(e.getSourceFile().fileName) === familyDescription))
          throw Error(`the tag guard ${entry.name} takes no ${familyDescription.tag.constants.enum} of the family ${familyDescription.marker}`);
        return enumMembersOf(enums, name.text);
      }
      for (const d of (targetOf(checker, name)?.declarations ?? []).map(x => x.resolve()))
        if (d && ts.isInterfaceDeclaration(d)) {
          const fam = familyFrom(d);
          if (fam && fam.table.description === familyDescription) return fam.constants;
        }
      throw Error(`the guard ${entry.name} takes no member of the family ${familyDescription.marker}`);
    };
    // The run's tag selection (HOST-FAMILIES.md, "Residuals"): one for every
    // module the run lowers, the tag values its candidate modules name. These
    // are the checked file and, transitively, each program module it imports
    // a function from by a value import (`importedModules` in
    // fragment-parse.mts, the modules the run may lower); a module named
    // there that the run leaves out keeps the selection. A module names the
    // tag constants it compares and its `case` labels, and the tags of the
    // family types it names whose tag is a set of literals. Given when an
    // imported module of the run is lowered.
    const closure = (): SourceFile[] => {
      const files: SourceFile[] = [];
      const visit = (file: SourceFile): void => {
        if (files.includes(file) || !programFile(file)) return;
        files.push(file);
        for (const statement of file.statements) {
          if (!ts.isImportDeclaration(statement)) continue;
          const clause = statement.importClause;
          if (!clause || (clause.phaseModifier === ts.SyntaxKind.TypeKeyword)) continue;
          const bindings = clause.namedBindings;
          const names = [...(clause.name ? [clause.name] : []),
            ...(bindings && ts.isNamedImports(bindings) ? bindings.elements.filter(e => !e.isTypeOnly).map(e => e.name) : [])];
          for (const name of names)
            for (const declaration of (targetOf(checker, name)?.declarations ?? []).map(x => x.resolve())) {
              if (!declaration || !ts.isFunctionDeclaration(declaration) || !declaration.body) continue;
              visit(declaration.getSourceFile());
            }
        }
      };
      visit(client);
      return files;
    };
    const scanSelection = (files: readonly SourceFile[]): Map<string, readonly TagValue[]> => {
      // The tag values found, by the marker of their family.
      const foundBy = new Map<string, Set<TagValue>>();
      const add = (description: FamilyDescription, value: TagValue): void => {
        const set = foundBy.get(description.marker) ?? new Set<TagValue>();
        foundBy.set(description.marker, set);
        set.add(value);
      };
      const constant = (expression: Node): void => {
        while (ts.isParenthesizedExpression(expression)) expression = expression.expression;
        if (!ts.isPropertyAccessExpression(expression) || !ts.isIdentifier(expression.name)) return;
        const declaration = targetOf(checker, expression.name)?.declarations[0]?.resolve();
        const description = declaration ? familyOfFile(declaration.getSourceFile().fileName) : null;
        if (!declaration || !ts.isEnumMember(declaration) || !description) return;
        const owner = declaration.parent;
        if (!ts.isEnumDeclaration(owner)) return;
        const family = families.get(description);
        if (family ? !family.enums.includes(owner) : owner.name.text !== description.tag.constants.enum) return;
        const value = checker.getConstantValue(declaration);
        if (typeof value === description.tag.primitive && value !== undefined) add(description, value);
      };
      const seenAliases = new Set<Node>();
      const namedType = (type: TypeNode): void => {
        if (ts.isParenthesizedTypeNode(type)) namedType(type.type);
        else if (ts.isUnionTypeNode(type)) type.types.forEach(namedType);
        else if (ts.isTypeReferenceNode(type)) named(type);
      };
      const named = (reference: ts.TypeReferenceNode): void => {
        const name = memberName(reference.typeName);
        if (!name) return;
        for (const d of (targetOf(checker, name)?.declarations ?? []).map(x => x.resolve())) {
          if (!d || !isHostFile(d.getSourceFile().fileName)) continue;
          if (ts.isTypeAliasDeclaration(d) && !d.typeParameters?.length && !seenAliases.has(d)) {
            seenAliases.add(d);
            namedType(d.type);
          }
          if (!ts.isInterfaceDeclaration(d)) continue;
          const fam = familyFrom(d);
          if (!fam) continue;
          const tag = fam.table.tagOf(d);
          const [argument] = reference.typeArguments ?? [];
          const values = tag.k === "literal" ? tag.values
            : tag.k === "parameter" && argument ? fam.literals(argument) ?? [] : [];
          for (const v of values) add(fam.table.description, v);
        }
      };
      const equality: readonly ts.SyntaxKind[] = [ts.SyntaxKind.EqualsEqualsEqualsToken,
        ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken];
      // A name TypeScript binds to a listed guard of an active family names
      // the guard's tag set, called or passed as a value (HOST-FAMILIES.md,
      // "Calls").
      const guardNames = new Set(activeFamilies().flatMap(d => d.guards.guards.map(g => g.name)));
      const guardName = (name: Identifier): void => {
        if (!guardNames.has(name.text)) return;
        const declaration = targetOf(checker, name)?.declarations[0]?.resolve();
        if (!declaration || !ts.isFunctionDeclaration(declaration) || !declaration.name) return;
        const entry = selectionGuard(declaration.getSourceFile().fileName, declaration.name.text);
        if (!entry) return;
        const constants = guardConstants(declaration, entry);
        for (const tag of entry.tags) {
          const value = constants.find(c => c.name === tag)?.value;
          if (value !== undefined) add(familyOfGuard(entry), value);
        }
      };
      const visit = (node: Node): void => {
        if (ts.isBinaryExpression(node) && equality.includes(node.operatorToken.kind)) {
          constant(node.left);
          constant(node.right);
        }
        if (ts.isIdentifier(node)) guardName(node);
        if (ts.isCaseClause(node)) constant(node.expression);
        if (ts.isTypeReferenceNode(node)) named(node);
        node.forEachChild(visit);
      };
      files.forEach(visit);
      return new Map([...foundBy].map(([marker, values]) => [marker, [...values].sort(compareTags)]));
    };
    let scanned: ReadonlyMap<string, readonly TagValue[]> | null = null;
    const scan = (): ReadonlyMap<string, readonly TagValue[]> => scanned ??= scanSelection(closure());
    const given = options.familySelection;
    // The selection is read here alone, by family.
    const selected = (marker: string): readonly TagValue[] | undefined => given ? given(marker) : scan().get(marker);
    const selectionSets = new Map<string, ReadonlySet<TagValue>>();
    const familyOf = (node: InterfaceDeclaration): { table: FamilyTable; selection: ReadonlySet<TagValue> } | null => {
      const found = familyFrom(node);
      if (!found) return null;
      const marker = found.table.description.marker;
      const set = selectionSets.get(marker) ?? new Set(selected(marker) ?? []);
      selectionSets.set(marker, set);
      return { table: found.table, selection: set };
    };
    // The type an enum's name denotes where `at` writes it
    // (SOURCE-CONTRACTS.md, "Enums"; COMPILER-API.md, reading rule 3): at a
    // position of a host declaration, of an enum with a numeric member,
    // `number`, since TypeScript admits any number there and the flag enums
    // hold combinations; elsewhere, and for an enum of strings alone, which
    // TypeScript admits nothing else at, the union of its members' types.
    const enumTypeAt = (identifier: Identifier, at: SourceFile, span: Span): TypeTerm | null => {
      const enums = enumsOf(identifier);
      if (!enums) return null;
      const what = `${idOf(at)}#${identifier.text}`;
      const members = enumMembersOf(enums, what);
      if (isHostFile(at.fileName) && !members.every(m => typeof m.value === "string"))
        return { k: "atom", name: "number", span };
      const parts = members.map((m): TypeTerm =>
        m.value === undefined ? { k: "atom", name: "number", span } : literalTerm(m.value, span));
      return parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
    };
    // `E.M`, an enum member's literal type, where `E` names an enum; and
    // `typeof E`, the enum's object.
    // The enum named directly or as a namespace member.
    const enumerated = (node: TypeNode, span: Span): TypeTerm | null => {
      if (ts.isTypeQueryNode(node) && !node.typeArguments?.length) {
        const named = memberName(node.exprName);
        const enums = named ? enumsOf(named) : null;
        return named && enums ? enumMembersTerm(enumMembersOf(enums, named.text), span, enumReverse(enums, enums[0]?.name.text ?? named.text)) : null;
      }
      if (!ts.isTypeReferenceNode(node) || !ts.isQualifiedName(node.typeName)) return null;
      const owner = memberName(node.typeName.left);
      const enums = owner ? enumsOf(owner) : null;
      if (!owner || !enums) return null;
      const name = node.typeName.right.text;
      const member = enumMembersOf(enums, owner.text).find(m => m.name === name);
      if (!member) throw Error(`${owner.text} has no member ${name}`);
      return member.value === undefined ? { k: "atom", name: "number", span } : literalTerm(member.value, span);
    };
    const resolveDeclaration = (identifier: Identifier, what: string): Node => {
      const nodes = resolveDeclarations(identifier, what);
      const [node] = nodes;
      if (nodes.length !== 1 || !node)
        throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
      return node;
    };
    const awaited = (reference: ts.TypeReferenceNode): boolean => {
      if (!ts.isIdentifier(reference.typeName)) return false;
      const target = targetOf(checker, reference.typeName);
      const declarations = target?.declarations.map(d => d.resolve()) ?? [];
      const [only] = declarations;
      return declarations.length === 1 && !!only && ts.isTypeAliasDeclaration(only) &&
        only.name.text === "Awaited" && libraryFile(only.getSourceFile());
    };
    // Whether an alias reaches `Awaited` through the aliases its body names,
    // each alias followed once along the walk.
    const associatedAlong = (node: TypeAliasDeclaration, seen: Set<TypeAliasDeclaration>): boolean => {
      if (seen.has(node)) return false;
      seen.add(node);
      const visit = (part: Node): boolean => {
        if (ts.isTypeReferenceNode(part)) {
          if (awaited(part)) return true;
          const target = ts.isIdentifier(part.typeName) ? targetOf(checker, part.typeName)?.declarations[0]?.resolve() : undefined;
          if (target && ts.isTypeAliasDeclaration(target) && associatedAlong(target, seen)) return true;
        }
        return part.forEachChild(visit) ?? false;
      };
      return visit(node.type);
    };
    // Each alias's answer, walked once: every reference to an alias asks.
    const associated = new Map<TypeAliasDeclaration, boolean>();
    const associatedAlias = (node: TypeAliasDeclaration): boolean => {
      const known = associated.get(node);
      if (known !== undefined) return known;
      const result = associatedAlong(node, new Set());
      associated.set(node, result);
      return result;
    };
    // An interface declared several times is one interface with every
    // declaration's members, as TypeScript merges it. Its type parameters are
    // positional: each declaration binds a prefix of the longest list (the
    // others have defaults, which TypeScript checks), under the same names,
    // and its members are read with the binders it states. The first
    // declaration stating the longest list is its identity. A same-named
    // value declaration, a constant or a function, is the name's other
    // meaning, which a type reference does not denote.
    const partners = new Map<TypeDeclaration, TypeDeclaration[]>();
    // The type aliases a name resolved to, by identity: a rest parameter
    // typed by one, and an indexed access into one's application, read it
    // through its equation (`restTerm`, `computed-types.mts`).
    const aliasNodes = new Map<string, ts.TypeAliasDeclaration>();
    const aliasKey = (identity: DeclarationIdentity) =>
      `${identity.module}#${identity.name}@${identity.span[0]}:${identity.span[1]}`;
    // A class merged with interfaces is one symbol too, the class its
    // identity, its instance contract every part's members (`collect`).
    const declarationOf = (nodes: readonly Node[], what: string): TypeDeclaration => {
      // A class merged with interfaces is the class; otherwise the
      // declaration binding the longest parameter list is the identity.
      const types0 = nodes.filter(isTypeDeclaration);
      const classes = types0.filter(ts.isClassDeclaration);
      const longest = Math.max(0, ...types0.map(n => n.typeParameters?.length ?? 0));
      const node = classes[0] ?? types0.find(n => (n.typeParameters?.length ?? 0) === longest);
      const types = node ? [node, ...types0.filter(n => n !== node)] : types0;
      if (!node || nodes.some(n => !isTypeDeclaration(n) && !ts.isVariableDeclaration(n) &&
            !ts.isFunctionDeclaration(n)) ||
          (types.length > 1 && !types.every(t => ts.isInterfaceDeclaration(t) || (t === node && classes.length === 1))))
        throw Error(types.length > 1 || nodes.length > 1
          ? `TypeScript found ${nodes.length} declarations for ${what}`
          : `${what} is not one type alias, interface or class`);
      const names = (n: TypeDeclaration) => (n.typeParameters ?? []).map(p => p.name.text);
      for (const part of types) {
        if (!part.name) throw Error(`${what} is not one type alias, interface or class`);
        const own = names(part), all = names(node);
        if (own.length > all.length || own.some((n, i) => n !== all[i]))
          throw Error(`the merged declarations of ${what} have different type parameters`);
        clean(part, `${idOf(part.getSourceFile())}#${part.name.text}`);
      }
      partners.set(node, types);
      if (ts.isTypeAliasDeclaration(node)) aliasNodes.set(aliasKey(identityOf(node)), node);
      return node;
    };
    const lookup = (identifier: Identifier, what: string): TypeDeclaration =>
      declarationOf(resolveDeclarations(identifier, what), what);
    // The type alias a reference names, if it names one the program declares.
    const aliasOf = (reference: ts.TypeReferenceNode): TypeAliasDeclaration | null => {
      if (!ts.isIdentifier(reference.typeName)) return null;
      try {
        const node = lookup(reference.typeName, reference.typeName.text);
        return ts.isTypeAliasDeclaration(node) ? node : null;
      } catch (error) {
        passToolFailure(error);
        return null;
      }
    };
    // A standard library type read at its meaning (`LibraryType`). Every
    // declaration TypeScript binds the name to must be the library's, so a
    // client that declares its own `Array`, merging into the global one, is
    // read as any other interface.
    const library = (identifier: Identifier, what: string): LibraryType | null => {
      const nodes = (targetOf(checker, identifier)?.declarations ?? []).map(d => d.resolve());
      // The host package's `NodeArray<T>` (COMPILER-API.md, "Node lists"): a
      // host type of its own, a node list read as a dense readonly array of
      // its elements. Its heritage and members are not read.
      if (nodes.length && nodes.every(n => !!n && ts.isInterfaceDeclaration(n) && n.name.text === hostNodeList &&
          compilerApiFile(n.getSourceFile().fileName)))
        return { k: "array", readonly: true, dense: true };
      const types: TypeDeclaration[] = [];
      for (const node of nodes) {
        if (!node || !libraryFile(node.getSourceFile())) return null;
        if (isTypeDeclaration(node)) types.push(node);
      }
      const [first] = types;
      const name = first?.name?.text;
      if (!first || !name || types.some(t => t.name?.text !== name)) return null;
      const cleanAll = () => types.forEach(part => clean(part, `${idOf(part.getSourceFile())}#${name}`));
      if ((name === "Array" || name === "ReadonlyArray") && types.every(ts.isInterfaceDeclaration)) {
        cleanAll();
        return { k: "array", readonly: name === "ReadonlyArray" };
      }
      let body = types.length === 1 && ts.isTypeAliasDeclaration(first) ? first.type : undefined;
      while (body && ts.isParenthesizedTypeNode(body)) body = body.type;
      if (!body || !ts.isMappedTypeNode(body)) return null;
      cleanAll();
      // The alias's parameters are positional in its template, and its
      // equation may name nothing else. Its bounds are TypeScript's to check
      // at each reference; only string keys expand.
      const source = first.getSourceFile();
      const where = `${idOf(source)}#${name}`;
      const parameters = (first.typeParameters ?? []).map(p => p.name.text);
      const template = mapped({ source, annotation: false,
        fail: (_node, message) => { throw Error(`${message} in ${where} for ${what}`); },
        named: (node, span) => {
          const index = ts.isIdentifier(node.typeName) ? parameters.indexOf(node.typeName.text) : -1;
          if (index < 0 || node.typeArguments?.length) throw Error(`${where} names a type outside its template`);
          return { k: "parameter", index, span };
        } }, body);
      return { k: "mapped", parameters: parameters.length, template };
    };
    // The standard library's `Function`: a value with call or construct code,
    // and nothing more is known. Its declared members are dropped, which is a
    // supertype of TypeScript's `Function`; TypeScript's own special case,
    // that every callable meets it, is the equation.
    const equation = (node: TypeDeclaration): TypeTerm | null => {
      const source = node.getSourceFile();
      const parts = partners.get(node) ?? [node];
      const library = ts.isInterfaceDeclaration(node) && !node.typeParameters?.length &&
        parts.every(part => libraryFile(part.getSourceFile()));
      if (library && node.name.text === "Function") return { k: "callable", span: [node.getStart(source), node.end] };
      return library ? libraryRegExp(node.name.text, parts) : null;
    };
    // The library's `RegExp`, `RegExpExecArray` and `RegExpMatchArray`, read
    // as `regexp.mts` states them; `RegExp`'s members it states must be
    // declared as reviewed.
    const libraryRegExp = (name: string, parts: readonly TypeDeclaration[]): TypeTerm | null => {
      if (name === "RegExp") {
        const members = parts.flatMap(part => ts.isInterfaceDeclaration(part)
          ? part.members.map(m => m.getText(part.getSourceFile()).trim()) : []);
        for (const { name: member, text } of reviewedRegExpMembers)
          if (!members.includes(text)) throw Error(`RegExp.${member} is not declared as reviewed: ${text}`);
      }
      return libraryRegExpTerm(name, () => regexpKeys());
    };
    // A computed key names a `unique symbol` constant. Each such declaration
    // is listed once, and its position in the list is the symbol's identity.
    // A mapped type's keys as TypeScript computes them, where they are a
    // union of literals and primitives.
    const keyTypeOf = (node: TypeNode): TypeTerm | null => {
      computedContext.captures(node);
      const type = checker.getTypeFromTypeNode(node);
      return type ? literalUnion(type, [node.getStart(node.getSourceFile()), node.end]) : null;
    };
    // A mapped type over `keyof X` as TypeScript resolves it: each property
    // with its modifiers, readonly where the mapping makes it so
    // (`checkFlags & 8`), or null where it resolves to no property.
    const mappedModifiersOf = (node: ts.MappedTypeNode): MappedMember[] | null => {
      computedContext.captures(node);
      const type = checker.getTypeFromTypeNode(node);
      const members = type ? checker.getPropertiesOfType(type).map(p => ({ name: p.name,
        optional: (p.flags & SymbolFlags.Optional) !== 0, readonly: (p.checkFlags & 8) !== 0 })) : [];
      return members.length ? members : null;
    };
    // The key an entity of a string or number literal type names, as an enum
    // member or a constant does: its value, a number at its canonical
    // spelling.
    const literalKeyOf = (name: Identifier | ts.PropertyAccessExpression): string | null => {
      const type = checker.getTypeAtLocation(name);
      if (!type) return null;
      if (type.isStringLiteralType()) return type.value;
      if (type.isNumberLiteralType() && Number.isFinite(type.value)) return numericKey(String(type.value));
      return null;
    };
    // Whether a name denotes a standard library value, such as `Symbol`.
    const isLibraryValue = (name: Identifier): boolean => {
      const nodes = (targetOf(checker, name)?.declarations ?? []).map(d => d.resolve());
      return nodes.length > 0 && nodes.every(n => !!n && libraryFile(n.getSourceFile()));
    };
    const symbols: DeclarationIdentity[] = [];
    const symbolIndex = new Map<string, number>();
    // A well-known symbol such as `Symbol.iterator` is a readonly property
    // declared `unique symbol`, and that property is its identity.
    const symbolOf = (written: Identifier | ts.PropertyAccessExpression): number => {
      const name = ts.isIdentifier(written) ? written : written.name;
      if (!ts.isIdentifier(name)) throw Error("a computed key names a symbol");
      const what = `[${ts.isIdentifier(written) ? written.text : `${written.expression.getText()}.${name.text}`}]`;
      const node = resolveDeclaration(name, what);
      const type = ts.isVariableDeclaration(node) || ts.isPropertySignatureDeclaration(node) ? node.type : undefined;
      const constant = ts.isVariableDeclaration(node) && ts.isVariableDeclarationList(node.parent) &&
        !!(node.parent.flags & ts.NodeFlags.Const);
      const property = ts.isPropertySignatureDeclaration(node) && !node.postfixToken &&
        node.modifiers?.length === 1 && node.modifiers[0]?.kind === ts.SyntaxKind.ReadonlyKeyword;
      if (!(constant || property) || !node.name || !ts.isIdentifier(node.name) ||
          !type || !ts.isTypeOperatorNode(type) || type.operator !== ts.SyntaxKind.UniqueKeyword ||
          type.type.kind !== ts.SyntaxKind.SymbolKeyword)
        throw Error(`the computed key ${what} is not a unique symbol constant`);
      const source = node.getSourceFile();
      clean(node, `${idOf(source)}#${node.name.text}`);
      const identity: DeclarationIdentity = { module: idOf(source), name: node.name.text,
        span: [node.getStart(source), node.end] };
      // Which symbol a constant holds is what made it. `Symbol()` makes a
      // fresh one, its declaration's own; `Symbol.for("k")` the registry's
      // for "k", which every constant made so holds, so that string is its
      // identity. TypeScript also types a constant made otherwise, by any
      // value asserted to be one, a unique symbol, whose symbol may be any
      // other's. A declared constant (`declare const`) or property holds
      // its own, as its type states: an assumption.
      const initializer = ts.isVariableDeclaration(node) ? node.initializer : undefined;
      const library = (callee: Node, name: string): boolean => ts.isIdentifier(callee)
        ? callee.text === name && isLibraryValue(callee)
        : ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) &&
          ts.isIdentifier(callee.name) && `${callee.expression.text}.${callee.name.text}` === name &&
          isLibraryValue(callee.expression);
      const [registry, ...more] = initializer && ts.isCallExpression(initializer) &&
        library(initializer.expression, "Symbol.for") ? initializer.arguments : [];
      const key = registry && !more.length && (ts.isStringLiteral(registry) ||
          ts.isNoSubstitutionTemplateLiteral(registry)) ? `Symbol.for ${JSON.stringify(registry.text)}`
        : !initializer || (ts.isCallExpression(initializer) && library(initializer.expression, "Symbol"))
          ? `${identity.module}#${identity.span[0]}:${identity.span[1]}`
          : null;
      if (key === null)
        throw Error(`the computed key ${what} names a constant made neither by \`Symbol()\` nor by ` +
          "`Symbol.for` of a string literal: which symbol it holds is not known");
      let index = symbolIndex.get(key);
      if (index === undefined) {
        index = symbols.length;
        symbols.push(identity);
        symbolIndex.set(key, index);
      }
      return index;
    };
    // A private name `#x` of a class member: a key no code outside the class
    // spells, as a symbol whose value no code obtains. It joins the symbols,
    // identified by the member declaring it; the class must be a top-level
    // declaration, evaluated once, so one member is one key.
    const privateOf = (member: Node): number => {
      const name = nameOf(member);
      const cls = member.parent;
      if (!name || !ts.isPrivateIdentifier(name) || !cls || !ts.isClassDeclaration(cls) || !cls.name ||
          !ts.isSourceFile(cls.parent))
        throw Error("a private name is declared by a member of a class at a file's top level");
      const source = member.getSourceFile();
      const identity: DeclarationIdentity = { module: idOf(source), name: `${cls.name.text}.${name.text}`,
        span: [name.getStart(source), name.end] };
      const key = `private ${identity.module}#${identity.span[0]}:${identity.span[1]}`;
      let index = symbolIndex.get(key);
      if (index === undefined) {
        index = symbols.length;
        symbols.push(identity);
        symbolIndex.set(key, index);
      }
      return index;
    };
    const privateNameOf = (name: ts.PrivateIdentifier): number => {
      if (name.parent && (ts.isPropertyDeclaration(name.parent) || ts.isMethodDeclaration(name.parent)) &&
          name.parent.name === name)
        return privateOf(name.parent);
      const members = (checker.getSymbolAtLocation(name)?.declarations ?? []).map(d => d.resolve());
      const [member] = members;
      if (members.length !== 1 || !member) throw Error(`the private name ${name.text} names no one member`);
      return privateOf(member);
    };
    // The type an imported value's declaration states, and the declarations
    // that type reaches, which join the graph.
    const valueStarts: TypeDeclaration[] = [];
    // Computed members have an equation only at closed arguments. Each
    // instance retains the declaration's whole admitted shape and heritage.
    const computedMembers = (node: TypeDeclaration): boolean => {
      if (ts.isTypeAliasDeclaration(node) || !node.typeParameters?.length) return false;
      const names = new Set(node.typeParameters.map(p => p.name.text));
      const mentions = (part: Node): boolean =>
        (ts.isTypeReferenceNode(part) && ts.isIdentifier(part.typeName) && names.has(part.typeName.text)) ||
        (part.forEachChild(c => mentions(c) || undefined) ?? false);
      const computed = (part: Node): boolean => {
        const alias = ts.isTypeReferenceNode(part) ? aliasOf(part) : null;
        if (ts.isTypeNode(part) && (computedForm(part) !== null ||
            (alias !== null && computedAlias(alias, aliasOf))) && mentions(part)) return true;
        return part.forEachChild(c => computed(c) || undefined) ?? false;
      };
      return (partners.get(node) ?? [node]).some(part =>
        (ts.isClassDeclaration(part) || ts.isInterfaceDeclaration(part)) && part.members.some(computed));
    };
    const instances = new Map<string, { node: TypeDeclaration; identity: DeclarationIdentity; args: readonly TypeTerm[]; use: Node }>();
    const instanceOf = (node: TypeDeclaration, args: readonly TypeTerm[], use: Node, span: Span): TypeTerm => {
      let open = false;
      args.forEach(arg => visitType(arg, term => { if (term.k === "binder" || term.k === "parameter") open = true; }));
      if (open) throw Error(`${node.name?.text}: computed members are read only at closed type arguments`);
      const original = identityOf(node);
      const key = JSON.stringify([original, args]);
      let instance = instances.get(key);
      if (!instance) {
        if (instances.size >= 256) throw Error("computed declaration instances exceed the graph budget of 256");
        const identity = { ...original, module: `tscert/instance/${instances.size}/${original.module}` };
        instance = { node, identity, args, use };
        instances.set(key, instance);
      }
      return { k: "reference", reference: { name: original.name, target: instance.identity, arguments: [], span }, args: [], span };
    };
    // The types of the values declared outside the program's sources, which
    // may reach no statement but a program class's (`externalStatements`).
    const externalTypes: { what: string; type: TypeTerm }[] = [];
    // The declarations of the values read, whose declared types are swept for
    // their written applications.
    const valueDeclarations: Node[] = [];
    // `captured` states a block type's captured parameter at a reference;
    // by default the binder of its spelling, which `binders` must hold.
    const valueScope = (node: Node, what: string, binders: string[] = [],
        captured?: (parameter: ts.TypeParameterDeclaration) => TypeTerm): TermScope => {
      const source = node.getSourceFile();
      return {
        source,
        annotation: false,
        awaited,
        stated: part => statement(part, null),
        associatedAlias: part => {
          const target = ts.isIdentifier(part.typeName) ? targetOf(checker, part.typeName)?.declarations[0]?.resolve() : undefined;
          return target && ts.isTypeAliasDeclaration(target) && associatedAlias(target) ? target : null;
        },
        // An alias's body, its parameters read as the reference's arguments.
        equation: (reference) => {
          const alias = reference.reference.target && aliasNodes.get(aliasKey(reference.reference.target));
          const parameters = alias ? parametersOf(alias).map(p => p.name.text) : [];
          if (!alias || reference.args.length !== parameters.length) return null;
          let body = alias.type;
          while (ts.isParenthesizedTypeNode(body)) body = body.type;
          if (!(ts.isArrayTypeNode(body) || ts.isTupleTypeNode(body) || ts.isTypeReferenceNode(body) ||
              (ts.isTypeOperatorNode(body) && body.operator === ts.SyntaxKind.ReadonlyKeyword)))
            return null;
          return instantiateAt(alias, reference.args, null)(body);
        },
        symbol: symbolOf,
        literalKey: literalKeyOf,
        computed: (part, pos, read) => computedType(computedContext, part, pos, read),
        keys: keyTypeOf,
        modifiers: mappedModifiersOf,
        enumerated,
        fail: (_node, message) => { throw Error(`${message} in ${what}`); },
        named: (part, pos, read) => {
          const name = memberName(part.typeName);
          if (!name) throw Error(`a qualified type reference in ${what}`);
          // A binder's spelling, unless TypeScript binds it to a type
          // declared in a nearer block.
          if (ts.isIdentifier(part.typeName) && binders.includes(name.text) &&
              !typeDeclarationsOf(name).some(isTypeDeclaration)) {
            if (part.typeArguments?.length) throw Error(`type parameter applied as constructor: ${name.text}`);
            return { k: "binder", name: name.text, span: pos };
          }
          const enumType = enumTypeAt(name, source, pos);
          if (enumType) {
            if (part.typeArguments?.length) throw Error(`an enum type takes no type arguments: ${name.text}`);
            return enumType;
          }
          const known = library(name, `${idOf(source)}#${name.text}`);
          if (known) return libraryTerm(known, libraryArguments(known, part.typeArguments ?? [], read, keyTypeOf), pos,
            message => { throw Error(`${message} in ${what}`); });
          const targetNode = lookup(name, `${idOf(source)}#${name.text}`);
          // An alias TypeScript computes from its parameters is the type it
          // computes at this reference's arguments.
          if (computedAlias(targetNode, aliasOf)) return computedType(computedContext, part, pos, read);
          const args = part.typeArguments ?? [];
          const target = `${identityOf(targetNode).module}#${name.text}`;
          const completed = completeArguments(targetNode, args.map(read), part, target, captured ?? (parameter => {
            if (!binders.includes(parameter.name.text))
              throw Error(`${target} closes over the type parameter ${parameter.name.text}, which ${what} does not bind`);
            return capturedAt(part, target)(parameter);
          }));
          if (computedMembers(targetNode)) return instanceOf(targetNode, completed, part, pos);
          valueStarts.push(targetNode);
          return { k: "reference", reference: { name: name.text, span: pos,
            arguments: args.map((arg): Span => [arg.getStart(source), arg.end]), target: identityOf(targetNode) },
            args: completed, span: pos };
        },
      };
    };
    // A generic declaration's binders, each bounded by what it extends; the
    // bound may name earlier binders.
    const bindersOf = (parameters: readonly ts.TypeParameterDeclaration[] | undefined, node: Node, what: string) => {
      const names: string[] = [];
      const typeParams = (parameters ?? []).map(p => {
        if (p.defaultType) throw Error(`a type parameter default of an imported value is outside the fragment: ${what}`);
        const bound = p.constraint ? typeTerm(valueScope(node, what, [...names]), p.constraint, p) : null;
        names.push(p.name.text);
        return { name: p.name.text, bound, resolution: null };
      });
      return { names, typeParams };
    };
    // The value TypeScript binds a name to, from every declaration it has.
    // A function declared with overloads is callable at exactly its
    // overloads, the declarations without a body (an implementation's own
    // signature is not callable from outside): the value meets each, so its
    // type is their intersection. A generic function has one signature. An
    // interface or type alias of the same name is the name's other meaning,
    // which a value reference does not denote.
    // A host value is the host's: its branded strings read where it produces
    // them (reading rule 5).
    const skipParenthesized = (e: Node): Node => ts.isParenthesizedExpression(e) ? skipParenthesized(e.expression) : e;
    // `guard` is the listed guard a client's import binds to (`bindingGuard`).
    const valueOf = (declared: readonly Node[], what: string, guard: GuardEntry | null = null, bound: boolean = false): Omit<ValueRoot, "binding"> => {
      const external = declared.some(n => !programFile(n.getSourceFile()) || ambient(n));
      if (external) externalReads++;
      let read: Omit<ValueRoot, "binding">;
      try {
        read = valueRead(declared, what, bound);
      } finally {
        if (external) externalReads--;
      }
      if (external) externalTypes.push({ what, type: read.type });
      return declared.some(n => isHostFile(n.getSourceFile().fileName))
        ? { ...read, type: guardReading(declared, hostBrands(read.type, true, isBrand, message => { throw Error(`${message} in ${what}`); }), guard) }
        : read;
    };
    // A guard of the compiler API's family (HOST-FAMILIES.md, "Guards as
    // values"): a listed one is read at the signature its entry gives, its
    // plain signature changing no value and no store and taking any further
    // arguments, beside the promise
    // signature of its tag set, the union of the family's shapes at those
    // tags (a node guard's, `guard.<name>` of the family's definitions) or
    // of the tags themselves (a tag guard's); any other host function
    // declaring a predicate at its plain signature, without it. A function
    // no predicate declares is as read.
    const guardReading = (declared: readonly Node[], type: TypeTerm, guard: GuardEntry | null): TypeTerm => {
      const [node] = declared;
      if (!node || declared.length !== 1 || !ts.isFunctionDeclaration(node) || !node.name || !node.type ||
          !ts.isTypePredicateNode(node.type)) return type;
      const forms = type.k === "intersection" ? type.parts : [type];
      const plain = forms.filter((f): f is Extract<TypeTerm, { k: "function" }> => f.k === "function" && f.effect.promise === null);
      const [one] = plain;
      if (!one || plain.length !== 1) throw Error(`the guard ${node.name.text} has no one plain signature`);
      const entry = guard;
      if (!entry || entry.name !== node.name.text) return one;
      const constants = guardConstants(node, entry);
      const values = entry.tags.map(name => {
        const value = constants.find(c => c.name === name)?.value;
        if (value === undefined) throw Error(`the family's constants hold no ${name}, a tag of ${entry.name}`);
        return value;
      });
      const span = one.span;
      let promised: TypeTerm;
      if (entry.kind === "tag") {
        const parts = values.map(v => literalTerm(v, span));
        const [only] = parts;
        promised = only && parts.length === 1 ? only : parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
      } else {
        const name = `guard.${entry.name}`;
        const marker = familyOfGuard(entry).marker;
        const promises = guardPromises.get(marker) ?? new Map<string, readonly TagValue[]>();
        guardPromises.set(marker, promises);
        promises.set(name, values);
        promised = { k: "reference", span, args: [], reference: { name, span, arguments: [],
          target: { module: `tscert/family/${marker}`, name, span: [0, 0] } } };
      }
      // Any further argument, which the entry states changes no answer, is
      // an element of a third signature's rest, of every value.
      const rest: TypeTerm = { k: "atom", name: "unknown", span };
      const plainForm = { ...one, effect: emptyEffect };
      return { k: "intersection", span, parts: [plainForm,
        { ...one, effect: { ...emptyEffect, promise: { guards: { param: 0 } } }, result: promised },
        { ...plainForm, rest }] };
    };
    const valueRead = (declared: readonly Node[], what: string, bound: boolean): Omit<ValueRoot, "binding"> => {
      const nodes = declared.filter(n => !ts.isInterfaceDeclaration(n) && !ts.isTypeAliasDeclaration(n));
      valueDeclarations.push(...nodes);
      const [node] = nodes;
      if (!node) throw Error(`unresolved value ${what}`);
      const source = node.getSourceFile();
      const span: Span = [node.getStart(source), node.end];
      // A node builder of the compiler API's package returns nodes outside
      // the node invariant (COMPILER-API.md, R2).
      const builder = compilerApiFile(source.fileName) ? installationPath(source.fileName) : null;
      if (builder !== null && hostNodeBuilders.includes(builder))
        throw Error(`${what} builds nodes outside the node invariant, which the compiler-API contract refuses (${builder})`);
      // An enum declared elsewhere is its object, read by `ambient-enum`
      // (SOURCE-CONTRACTS.md, "Enums"): its members, each at its value's
      // literal type, `number` where TypeScript computes none. A host enum is
      // read only where the contract lists it (`compiler-api.mts`, T5).
      const enums = nodes.filter(ts.isEnumDeclaration);
      if (enums.length) {
        if (enums.length !== nodes.length) throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
        if (enums.some(e => e.modifiers?.some(m => m.kind === ts.SyntaxKind.ConstKeyword)))
          throw Error(`the imported const enum ${what} has no object: its reads are its members' values, which TypeScript inlines`);
        const name = enums[0]?.name.text ?? what;
        if (enums.some(e => isHostFile(e.getSourceFile().fileName)) && !readableHostEnum(enums, name, bound))
          throw Error(`the host enum ${name} is not one the compiler-API contract reads (compiler-api.mts), nor a family's tag enum its runtime object matches`);
        return { declaration: { module: idOf(source), name, span }, construct: false, typeParams: [],
          type: enumMembersTerm(enumMembersOf(enums, what), span, enumReverse(enums, name)) };
      }
      if (nodes.length > 1) {
        const overloads = nodes.filter((n): n is ts.FunctionDeclaration => ts.isFunctionDeclaration(n) && !n.body);
        if (!overloads.length || !nodes.every(ts.isFunctionDeclaration) || nodes.length - overloads.length > 1)
          throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
        // A declaration's unit is certified at one signature: a statement on
        // an overload, or on the implementation, has no check, one overload
        // beside its implementation included.
        if (nodes.some(n => ts.isFunctionDeclaration(n) && statedResult(valueScope(n, what), n.type, n).stated))
          throw Error(`a statement (\`Within\`) on an overloaded declaration is outside the fragment: ${what}`);
        if (overloads.length > 1) {
          if (overloads.some(o => o.typeParameters?.length))
            throw Error(`an overloaded generic function is outside the fragment: ${what}`);
          const forms = overloads.flatMap(o => {
            const at: Span = [o.getStart(source), o.end];
            for (const part of [...o.parameters, ...(o.type ? [o.type] : [])])
              clean(part, `${idOf(source)}#${o.name?.text ?? what}`);
            return signatures(valueScope(o, what), o.parameters, o.type, o, at, true);
          });
          return { declaration: { module: idOf(source), name: overloads[0]?.name?.text ?? what, span },
            construct: false, typeParams: [], type: oneTerm(forms, span) };
        }
        return valueOf(overloads, what);
      }
      if (ts.isFunctionDeclaration(node) && node.name) {
        // Only the signature is the contract; the body is what is assumed,
        // so an error inside it is not the graph's.
        for (const part of [...(node.typeParameters ?? []), ...node.parameters, ...(node.type ? [node.type] : [])])
          clean(part, `${idOf(source)}#${node.name.text}`);
        const { names, typeParams } = bindersOf(node.typeParameters, node, what);
        return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false, typeParams,
          type: oneTerm(signature(valueScope(node, what, names), node.parameters, node.type, node, span, true), span) };
      }
      if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name)) {
        const list = node.parent;
        const constant = ts.isVariableDeclarationList(list) && (list.flags & ts.NodeFlags.Const) !== 0;
        // A constant initialized by a literal naming nothing states its type
        // by that literal (SOURCE-CONTRACTS.md, "Types stated by
        // annotations"): a primitive literal its literal type, an object
        // literal of such the record TypeScript infers. An array literal or
        // one `as const` is no type the reader states yet.
        if (constant && !node.type && node.initializer && literal(node.initializer)) {
          const type = checker.getTypeAtLocation(node.name);
          const term = type ? inferredTerm(checker, type, span) : null;
          if (!term)
            throw Error(`a declared value must be an annotated constant, function or class, or a constant initialized by a primitive literal or an object literal of such: ${what}`);
          clean(node, `${idOf(source)}#${node.name.text}`);
          return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false,
            typeParams: [], type: term };
        }
        // A constant initialized by a function literal states its type by
        // the literal's parameter and result annotations, as a function
        // declaration does; the body is what is assumed.
        const fn = node.initializer && skipParenthesized(node.initializer);
        if (constant && !node.type && fn && (ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) && fn.type &&
            fn.parameters.every(p => !!p.type)) {
          for (const part of [...(fn.typeParameters ?? []), ...fn.parameters, fn.type])
            clean(part, `${idOf(source)}#${node.name.text}`);
          const { names, typeParams } = bindersOf(fn.typeParameters, fn, what);
          return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false, typeParams,
            type: oneTerm(signature(valueScope(fn, what, names), fn.parameters, fn.type, fn, span, true), span) };
        }
        if (!constant || !node.type)
          throw Error(`a declared value must be an annotated constant, function or class: ${what}`);
        clean(node, `${idOf(source)}#${node.name.text}`);
        // A `unique symbol` constant holds the symbol its declaration names,
        // the one `typeof` it denotes (`symbolOf`): its value is that
        // singleton. One whose symbol is not known (made otherwise) is a
        // symbol.
        const type = node.type;
        const unique = ts.isTypeOperatorNode(type) && type.operator === ts.SyntaxKind.UniqueKeyword &&
          type.type.kind === ts.SyntaxKind.SymbolKeyword;
        const symbol = unique ? (() => { try { return symbolOf(node.name); } catch (error) { passToolFailure(error); return null; } })() : null;
        return { declaration: { module: idOf(source), name: node.name.text, span }, construct: false,
          typeParams: [], type: symbol === null ? typeTerm(valueScope(node, what), type, node)
            : { k: "unique", symbol, span: [type.getStart(source), type.end] } };
      }
      if (ts.isClassDeclaration(node) && node.name) {
        clean(node, `${idOf(source)}#${node.name.text}`);
        const { names, typeParams } = bindersOf(node.typeParameters, node, what);
        const scope = valueScope(node, what, names);
        const constructor = node.members.find(ts.isConstructorDeclaration);
        // A defaulted parameter may be omitted: `undefined` is what a short
        // call binds there, and the default replaces it.
        const params = (constructor?.parameters ?? []).map(p => {
          if (!ts.isIdentifier(p.name) || p.dotDotDotToken)
            throw Error(`an imported class constructor needs plain parameters: ${what}`);
          const type = typeTerm(scope, p.type, p);
          return p.questionToken || p.initializer ? optionalTerm(type, [p.getStart(source), p.end]) : type;
        });
        const identity = identityOf(node);
        valueStarts.push(node);
        const nameSpan: Span = [node.name.getStart(source), node.name.end];
        return { declaration: identity, construct: true, typeParams, type: { k: "constructor",
          effect: ordinaryEffect, params, rest: null,
          result: { k: "reference", reference: { name: node.name.text, span: nameSpan,
            arguments: names.map(() => nameSpan), target: identity },
            args: names.map(name => ({ k: "binder", name, span: nameSpan })), span: nameSpan }, span } };
      }
      throw Error(`${what} is not an annotated constant, function or class`);
    };
    // A Node module function the reviewed overlay lists (`library-modules.mts`):
    // the declarations TypeScript binds the import to are overloads in Node's
    // declarations, each entry's among them exactly as reviewed. The value is
    // the entries' statements; the declarations' types are not read.
    const moduleValue = (declared: readonly Node[], entries: readonly ModuleEntry[], what: string):
        Omit<ValueRoot, "binding"> => {
      // A function's overloads, or the methods of the object a module
      // exports whole (`export = path`, `path.PlatformPath`'s); a namespace
      // merged into a function (`realpathSync.native`) is its other members.
      const callable = declared.filter(n => !ts.isModuleDeclaration(n));
      // A constant the module's exported object declares (`path.sep`): the
      // value has the entry's stated type.
      if (entries.length && entries.every(e => e.constant)) {
        const [entry] = entries;
        if (entries.length !== 1 || entries.some(e => e.stated.binders.length || e.stated.params.length || e.stated.rest || e.effect))
          throw Error(`${what} is reviewed as a constant with parameters or an effect`);
        const match = entry && callable.length === 1 ? callable.find(n => ts.isPropertySignatureDeclaration(n) &&
          idOf(n.getSourceFile()).includes("@types/node/") && n.getText(n.getSourceFile()) === entry.signature) : undefined;
        if (!entry || !match) throw Error(`${what} is not declared as reviewed: ${entries.map(e => e.signature).join(" ")}`);
        const source = match.getSourceFile();
        const span: Span = [match.getStart(source), match.end];
        return { declaration: { module: idOf(source), name: what, span }, construct: false, typeParams: [],
          type: { ...entry.stated.result, span } };
      }
      if (entries.some(e => e.constant)) throw Error(`${what} is reviewed both as a constant and as a function`);
      // A constant whose declared type is one interface of Node's
      // declarations (`const statSync: StatSyncFn`): its overloads are the
      // interface's call signatures, every member it has besides.
      const [variable] = callable;
      const typeName = variable && callable.length === 1 && ts.isVariableDeclaration(variable) && variable.type &&
        ts.isTypeReferenceNode(variable.type) && ts.isIdentifier(variable.type.typeName) && !variable.type.typeArguments?.length
        ? variable.type.typeName : undefined;
      const callTyped = typeName ? typeDeclarationsOf(typeName) : [];
      const viaInterface = callTyped.length === 1 && callTyped.every(ts.isInterfaceDeclaration)
        ? callTyped.flatMap(d => d.members) : null;
      const overloads = viaInterface
        ? viaInterface.filter(ts.isCallSignatureDeclaration)
        : callable.filter((n): n is ts.FunctionDeclaration | ts.MethodSignatureDeclaration =>
          (ts.isFunctionDeclaration(n) && !n.body) || ts.isMethodSignatureDeclaration(n));
      if (viaInterface && overloads.length !== viaInterface.length)
        throw Error(`${what}'s declared type has members besides its call signatures`);
      if (!overloads.length || (!viaInterface && overloads.length !== callable.length) ||
          overloads.some(o => !idOf(o.getSourceFile()).includes("@types/node/")))
        throw Error(`${what} is not a function Node's declarations declare, as the reviewed overlay of library modules states it`);
      const forms = entries.map(entry => {
        const match = overloads.find(o => o.getText(o.getSourceFile()) === entry.signature);
        if (!match) throw Error(`${what} is not declared as reviewed: ${entry.signature}`);
        const source = match.getSourceFile();
        const span: Span = [match.getStart(source), match.end];
        const term: Extract<TypeTerm, { k: "function" }> = { k: "function", effect: entry.effect ?? ordinaryEffect, receiver: null,
          params: entry.stated.params, rest: entry.stated.rest ?? null, result: entry.stated.result, span };
        return { module: idOf(source), span, term };
      });
      const [first] = forms;
      if (!first) throw Error(`${what} has no reviewed overload`);
      return { declaration: { module: first.module, name: what, span: first.span }, construct: false, typeParams: [],
        type: oneTerm(forms.map(f => f.term), first.span) };
    };
    // Computed types (`computed-types.mts`): an annotation they reach is read
    // where it is declared, as an imported value's is, and must be clean.
    const computedContext: ComputedContext = {
      checker,
      annotation: (type, at, binders) => {
        const what = `${idOf(at.getSourceFile())}#${type.getText(at.getSourceFile())}`;
        clean(type, what);
        return typeTerm(valueScope(at, what, binders), type, at);
      },
      value: (nodes, what) => valueOf(nodes, what),
      alias: aliasOf,
      // A block alias's captured arguments are the binders at the use.
      applied: (alias, args, use) => instantiateAt(alias, [...capturedOf(alias).map(capturedAt(use,
        `${idOf(alias.getSourceFile())}#${alias.name.text}`)), ...args], use),
      equation: reference => valueScope(client, "an alias's equation").equation?.(reference) ?? null,
      // Each block type the form names, at the binders it closes over.
      captures: node => {
        const visit = (n: Node): void => {
          if (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName))
            for (const d of typeDeclarationsOf(n.typeName))
              if (inBlock(d)) capturedOf(d).forEach(capturedAt(n, `${idOf(d.getSourceFile())}#${n.typeName.text}`));
          n.forEachChild(visit);
        };
        visit(node);
      },
      // A `unique symbol` type is the type of the one constant or readonly
      // property declaring it (`Symbol.iterator`'s is `SymbolConstructor`'s
      // `iterator`), which names its symbol as a computed key does.
      unique: type => {
        const nodes = (type.getSymbol()?.declarations ?? []).map(d => d.resolve());
        const [node, ...more] = nodes;
        const name = node && (ts.isVariableDeclaration(node) || ts.isPropertySignatureDeclaration(node)) &&
          node.name && ts.isIdentifier(node.name) ? node.name : null;
        if (!name || more.length)
          throw Error(`the unique symbol ${checker.typeToString(type)} is declared by no one constant`);
        return symbolOf(name);
      },
    };
    const roots: { root: TypeRoot; node: TypeDeclaration }[] = [];
    const values: ValueRoot[] = [];
    const typeDeclarationsOf = (name: Identifier): Node[] =>
      (targetOf(checker, name)?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node => !!d);
    // TypeScript's evaluation of a form in a declaration's parameter list at
    // an application (`type-probe.mts`).
    const probe = makeProbe({ program, checker }, probeProgram, name => symbolOf(name), (name, args, span) => {
      const node = lookup(name, name.text);
      if (args.length !== parametersOf(node).length)
        throw Error(`the computed type ${name.text} does not state every declaration argument`);
      if (computedMembers(node)) throw Error(`the computed result ${name.text} needs a written application to read its computed members`);
      valueStarts.push(node);
      return { k: "reference", reference: { name: name.text, target: identityOf(node), arguments: args.map(() => span), span }, args, span };
    });
    // A declaration's type parameters by position, its merged declarations
    // together, as TypeScript merges them: each position's name from the
    // declaration binding the longest list, its bound and default from a
    // declaration stating them (TypeScript requires those to agree).
    // A type declared in a block closes over the enclosing type parameters
    // its equation names, directly or through another block's type, each
    // one TypeScript resolves at its block, outermost first: they come
    // first among its parameters, each argument the binder itself, which
    // needs no bound (SOURCE-CONTRACTS.md, "Block-scoped type declarations").
    const nodeKey = (n: Node): string => `${n.getSourceFile().fileName}:${n.kind}:${n.pos}:${n.end}`;
    const sameNode = (a: Node, b: Node): boolean => nodeKey(a) === nodeKey(b);
    const resolvesTo = (parameter: ts.TypeParameterDeclaration, at: Node): boolean =>
      (checker.resolveName(parameter.name.text, SymbolFlags.Type, at, false)?.declarations ?? [])
        .some(d => { const n = d.resolve(); return !!n && sameNode(n, parameter); });
    const inBlock = (declaration: Node): boolean => {
      const block = declaration.parent;
      return isTypeDeclaration(declaration) && !!block && !ts.isSourceFile(block) && !ts.isModuleBlock(block);
    };
    // The type parameters a block's type names, through the block types it
    // names too, by node key.
    const mentioned = (declaration: Node, found: Set<string>, seen: Set<string>): void => {
      const name = nameOf(declaration);
      const parts = name && ts.isIdentifier(name) ? typeDeclarationsOf(name).filter(isTypeDeclaration) : [declaration];
      for (const part of parts) {
        if (seen.has(nodeKey(part))) continue;
        seen.add(nodeKey(part));
        const visit = (n: Node): void => {
          const spelled = ts.isTypeReferenceNode(n) ? n.typeName
            : ts.isExpressionWithTypeArguments(n) ? n.expression : null;
          if (spelled && ts.isIdentifier(spelled))
            for (const d of typeDeclarationsOf(spelled)) {
              if (ts.isTypeParameterDeclaration(d)) found.add(nodeKey(d));
              else if (inBlock(d)) mentioned(d, found, seen);
            }
          n.forEachChild(visit);
        };
        visit(part);
      }
    };
    const captures = new Map<string, ts.TypeParameterDeclaration[]>();
    const capturedOf = (declaration: Node): ts.TypeParameterDeclaration[] => {
      const block = declaration.parent;
      if (!inBlock(declaration) || !block) return [];
      const known = captures.get(nodeKey(declaration));
      if (known) return known;
      const found = new Set<string>();
      mentioned(declaration, found, new Set());
      const groups: ts.TypeParameterDeclaration[][] = [];
      for (let at: Node | undefined = block; at; at = at.parent)
        groups.unshift(childrenOf(at, "typeParameters").filter((p): p is ts.TypeParameterDeclaration =>
          ts.isTypeParameterDeclaration(p) && found.has(nodeKey(p))));
      const result = groups.flat();
      // One named only through another block's type, which a nearer
      // declaration hides at this block, has no argument here.
      const hidden = result.find(p => !resolvesTo(p, block));
      if (hidden) throw Error(`${idOf(declaration.getSourceFile())}#${nameOf(declaration)?.getText(declaration.getSourceFile()) ?? "a type"} ` +
        `names a type closing over the type parameter ${hidden.name.text}, which a nearer declaration of that name hides at its block`);
      captures.set(nodeKey(declaration), result);
      return result;
    };
    const parametersOf = (declaration: Node): MergedParameter[] => {
      const name = nameOf(declaration);
      const parts = name && ts.isIdentifier(name) ? typeDeclarationsOf(name).filter(isTypeDeclaration) : [];
      const own = isTypeDeclaration(declaration) ? [declaration] : [];
      const captured = capturedOf(declaration).map((p): MergedParameter =>
        ({ name: p.name, constraint: undefined, default: undefined, captured: true }));
      return [...captured, ...mergedParameters(parts.length ? parts : own).map(merged => ({ name: merged.parameter.name,
        constraint: merged.bound?.at.constraint, default: merged.default?.at.defaultType }))];
    };
    // A block type's captured parameter at a use outside a declaration's
    // body: the binder itself, which TypeScript must resolve its spelling
    // to there.
    const capturedAt = (use: Node, what: string) => (parameter: ts.TypeParameterDeclaration): TypeTerm => {
      if (!resolvesTo(parameter, use))
        throw Error(`${what} closes over the type parameter ${parameter.name.text}, which a nearer declaration of that name hides here`);
      return { k: "binder", name: parameter.name.text, span: [use.getStart(use.getSourceFile()), use.end] };
    };
    // A declaration's bound or default read at an application's arguments:
    // each parameter its argument; a computed form naming the parameters,
    // or a computed alias's application naming them, what TypeScript
    // computes for it at the application `use`; any other computed form
    // what TypeScript computes for it where it is written.
    const instantiateAt = (declaration: Node, args: readonly TypeTerm[], use: Node | null): (node: TypeNode) => TypeTerm => {
      const source = declaration.getSourceFile();
      const what = `${idOf(source)}#${nameOf(declaration)?.getText(source) ?? "a declaration"}`;
      const merged = parametersOf(declaration);
      const parameters = merged.map(p => p.name.text);
      // An own parameter shadows a captured one of its spelling.
      const argumentOf = (part: Node): TypeTerm | undefined => {
        const index = ts.isTypeReferenceNode(part) && ts.isIdentifier(part.typeName) && !part.typeArguments?.length
          ? parameters.lastIndexOf(part.typeName.text) : -1;
        return index < 0 ? undefined : args[index];
      };
      const namesParameter = (n: Node): boolean =>
        (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) && parameters.includes(n.typeName.text)) ||
        (n.forEachChild(c => namesParameter(c) || undefined) ?? false);
      const outer = valueScope(declaration, what, [], parameter => {
        const index = merged.findIndex(p => p.name.parent && nodeKey(p.name.parent) === nodeKey(parameter));
        const argument = args[index];
        if (!argument) throw Error(`${what} has no argument for the captured type parameter ${parameter.name.text}`);
        return argument;
      });
      const evaluate: NonNullable<TermScope["computed"]> = (part, pos, read) => {
        if (!namesParameter(part)) return computedType(computedContext, part, pos, read);
        if (!use) throw Error(`${what}: ${part.getText(source)} names the declaration's parameters, ` +
          "and is evaluated only at an application written in source");
        if (merged.some(p => p.captured)) throw Error(`${what}: ${part.getText(source)} names the parameters of ` +
          "a type declared in a block, which TypeScript evaluates only where it closes over no type parameter");
        computedContext.captures(part);
        return probe({ declaration, parameters: merged, form: part, use, span: pos, what });
      };
      const scope: TermScope = { ...outer,
        named: (part, pos, read) => {
          const argument = argumentOf(part);
          if (argument) return argument;
          const alias = aliasOf(part);
          if (alias && computedAlias(alias, aliasOf) && namesParameter(part)) return evaluate(part, pos, read);
          return outer.named(part, pos, read);
        },
        computed: evaluate };
      return node => typeTerm(scope, node, declaration);
    };
    // The arguments of an application `use` of `declaration`: those written,
    // then each omitted one its parameter's default read at the arguments
    // before it (`instantiateAt`).
    // A block type's captured arguments come first, each the reader's
    // (`captured`); a reader stating none refuses such a type.
    const completeArguments = (declaration: Node, written: readonly TypeTerm[], use: Node | null,
        what: string, captured?: (parameter: ts.TypeParameterDeclaration) => TypeTerm): TypeTerm[] => {
      const parameters = parametersOf(declaration);
      const closed = parameters.flatMap(p => {
        if (!p.captured) return [];
        const at = p.name.parent;
        if (!captured || !at || !ts.isTypeParameterDeclaration(at))
          throw Error(`${what} is declared in a block and closes over the type parameter ${p.name.text}, which this reading does not state`);
        return [captured(at)];
      });
      if (closed.length + written.length > parameters.length) throw Error(`${what} applied to too many type arguments`);
      const completed = [...closed, ...written];
      for (const parameter of parameters.slice(completed.length)) {
        if (!parameter.default) throw Error(`${what}'s ${parameter.name.text} has neither an argument nor a default`);
        completed.push(instantiateAt(declaration, completed, use)(parameter.default));
      }
      return completed;
    };
    // A module exporting a function merged with a namespace, read by its
    // default import (`import assert from "node:assert/strict"`): one value,
    // the function's call and the members the file calls, each the
    // declaration TypeScript resolves the call to, read at the reviewed
    // entry of its text (`library-modules.mts`). Every mention is a call of
    // the value or of a member.
    const assertionSpans: Span[] = [];
    const namespaceFunction = (binding: { name: string; at: Identifier; specifier: string; imported: string },
        nodes: readonly Node[]): Omit<ValueRoot, "binding"> | null => {
      const member = binding.imported === "default" ? undefined : binding.imported.slice("default.".length);
      const entries = moduleEntries(binding.specifier, "default");
      const what = `the default import of ${binding.specifier}`;
      const symbol = checker.getSymbolAtLocation(binding.at);
      if (!symbol) throw Error(`TypeScript binds no ${what}`);
      // The direct calls `assert(…)`; a member read `assert.m` is a binding
      // of its own (`namespace-members.mts`), found through `members`.
      const calls: ts.CallExpression[] = [];
      const find = (n: Node): void => {
        if (ts.isIdentifier(n) && n !== binding.at && n.text === binding.name &&
            checker.getSymbolAtLocation(n)?.id === symbol.id && ts.isCallExpression(n.parent) && n.parent.expression === n)
          calls.push(n.parent);
        n.forEachChild(find);
      };
      if (member === undefined) find(client);
      else
        for (const use of (options.namespaceMembers ?? []).find(m => m.local === binding.name)?.uses ?? []) {
          const access = expressionAt(client, use.span);
          const call = access?.parent;
          if (!access || !call || !ts.isCallExpression(call) || call.expression !== access)
            throw Error(`${binding.name} is only called`);
          calls.push(call);
        }
      const spanOf = (node: Node): Span => [node.getStart(client), node.end];
      const entryAt = (call: ts.CallExpression, member: string | undefined): ModuleEntry => {
        const declaration = checker.getResolvedSignature(call)?.declaration?.resolve();
        const written = declaration ? declaration.getText(declaration.getSourceFile()) : "";
        const text = reviewedText(written);
        const entry = declaration ? entries.find(e => e.member === member && e.signature === written) : undefined;
        if (!entry)
          throw Error(`${member === undefined ? binding.name : `${binding.name}.${member}`}(…) is not declared as reviewed: ${text}`);
        return entry;
      };
      // A statement call with no message or a literal one, read as a test.
      const lowered = (call: ts.CallExpression): boolean => {
        const [value, message, ...more] = call.arguments;
        return ts.isExpressionStatement(call.parent) && call.parent.expression === call && !!value && !more.length &&
          !call.typeArguments?.length && !call.arguments.some(ts.isSpreadElement) &&
          (!message || ts.isStringLiteral(message) || ts.isNoSubstitutionTemplateLiteral(message));
      };
      const chosen = new Map<ModuleEntry, Span>();
      for (const call of calls) {
        if (call.questionDotToken) throw Error(`${binding.name} is called without an optional chain`);
        const entry = entryAt(call, member);
        const span = spanOf(call);
        chosen.set(entry, span);
        if (entry.lowering === "test" && lowered(call)) {
          assertionSpans.push(span);
          options.assertionCall?.(span);
        }
      }
      // An entry's forms: its statement, and where it states a promise, the
      // promise signature beside it.
      const forms = (entry: ModuleEntry, receiver: TypeTerm | null, at: Span): FunctionTerm[] => {
        const effect = entry.effect ?? ordinaryEffect;
        const plain: FunctionTerm = { k: "function", effect, receiver, params: entry.stated.params,
          rest: entry.stated.rest ?? null, result: entry.stated.result, span: at };
        return entry.promise
          ? [plain, { ...plain, effect: { ...effect, promise: { asserts: { param: entry.promise.param } } }, result: entry.promise.type }]
          : [plain];
      };
      // The value: the forms of each overload its calls resolve to; a generic
      // statement's binders are the value's type parameters, as an imported
      // generic function's are.
      const entriesChosen = [...chosen];
      const binders = entriesChosen.flatMap(([entry]) => entry.stated.binders);
      if (binders.length && entriesChosen.length > 1)
        throw Error(`${binding.name} selects a generic statement beside other overloads`);
      const signatures = entriesChosen.flatMap(([entry, at]) => forms(entry, null, at));
      const [first] = nodes;
      if (!first) throw Error(`TypeScript declares no ${what}`);
      const source = first.getSourceFile();
      const at: Span = [first.getStart(source), first.end];
      if (!signatures.length) return null;
      return { declaration: { module: idOf(source), name: member === undefined ? "default" : `default.${member}`, span: at },
        construct: false, typeParams: binders.map(name => ({ name, bound: null, resolution: null })),
        type: oneTerm(signatures, at) };
    };
    // The listed guard a client's import binds (HOST-FAMILIES.md, "Calls"):
    // what Node loads for it (`importedGuard`), resolved from the importing
    // module itself, where that is the very function activation checked; or,
    // where Node resolves a module of the program, that module's
    // `export { g } from "…"`, resolved again by Node from it. An import or a
    // re-export with attributes, a module Node resolves that the program
    // does not hold, or any other form of binding binds none.
    const programModule = (path: string): SourceFile | undefined => {
      const name = program.getSourceFileNames().find(n => orAbsent(realPath, n) === path);
      return name === undefined ? undefined : program.getSourceFile(name);
    };
    const reexported = (from: SourceFile, specifier: string, imported: string, depth: number):
        { description: FamilyDescription; value: unknown } | null => {
      if (depth > 16) return null;
      const statements = from.statements.filter((s): s is ts.ImportDeclaration | ts.ExportDeclaration =>
        (ts.isImportDeclaration(s) || ts.isExportDeclaration(s)) && s.moduleSpecifier !== undefined &&
        ts.isStringLiteral(s.moduleSpecifier) && s.moduleSpecifier.text === specifier);
      if (statements.some(s => s.attributes)) return null;
      const bound = importedExport(from.fileName, specifier, imported);
      if (!bound) return null;
      if (bound.description !== undefined) return bound;
      const module = programModule(bound.program);
      if (!module || module.isDeclarationFile || isHostFile(module.fileName)) return null;
      for (const s of module.statements) {
        if (!ts.isExportDeclaration(s) || s.isTypeOnly || !s.exportClause || !ts.isNamedExports(s.exportClause) ||
            !s.moduleSpecifier || !ts.isStringLiteral(s.moduleSpecifier)) continue;
        const element = s.exportClause.elements.find(e => !e.isTypeOnly && e.name.text === imported);
        if (element) return reexported(module, s.moduleSpecifier.text, element.propertyName?.text ?? element.name.text, depth + 1);
      }
      return null;
    };
    const bindingGuard = (binding: { specifier: string; imported: string; typeOnly: boolean }): GuardEntry | null => {
      const bound = binding.typeOnly ? null : reexported(client, binding.specifier, binding.imported, 0);
      return bound ? guardOfExport(bound.description, bound.value) : null;
    };
    // Whether an import of a host enum binds, as Node resolves it,
    // the object whose members the host contract checks against the
    // declaration (`hostEnumObject`), of the family whose installation
    // declares the enum.
    const boundHostEnum = (binding: { specifier: string; imported: string; typeOnly: boolean },
        enums: readonly ts.EnumDeclaration[]): boolean => {
      const [first] = enums;
      const description = first ? familyOfFile(first.getSourceFile().fileName) : null;
      const bound = binding.typeOnly ? null : reexported(client, binding.specifier, binding.imported, 0);
      return !!description && !!bound && bound.description === description && bound.value !== undefined && bound.value === hostEnumObject(description, first?.name.text ?? "");
    };
    for (const binding of importBindings(client, options.namespaceMembers ?? [])) {
      try {
        // A function with overloads is its several declarations; any other
        // name must have one.
        const nodes = resolveDeclarations(binding.at, binding.name);
        const enums = enumsOf(binding.at);
        if (enums) {
          options.importedEnum?.(binding.name, enumMembersOf(enums, binding.name), enumReverse(enums, enums[0]?.name.text ?? binding.name));
          if (!binding.typeOnly)
            values.push({ binding: { local: binding.name, imported: binding.imported,
              specifier: binding.specifier, span: binding.span }, ...valueOf(nodes, binding.name, bindingGuard(binding), boundHostEnum(binding, enums)) });
          continue;
        }
        const reviewed = moduleEntries(binding.specifier, binding.imported);
        // Node's assertion functions state promises their declarations alone
        // assert: a value of `node:assert` or `node:assert/strict` is read
        // through the latter's default import and its members alone, at
        // their reviewed entries, never at a declaration.
        const module = binding.specifier.startsWith("node:") ? binding.specifier.slice("node:".length) : binding.specifier;
        if (!binding.typeOnly && (module === "assert" || (module === "assert/strict" &&
            binding.imported !== "default" && !binding.imported.startsWith("default."))))
          throw Error(`${binding.name} of ${binding.specifier} is read through the default import of node:assert/strict alone`);
        if (!binding.typeOnly && (binding.imported === "default" || binding.imported.startsWith("default.")) &&
            moduleEntries(binding.specifier, "default").some(e => e.member !== undefined)) {
          const value = namespaceFunction(binding, nodes);
          if (value) values.push({ binding: { local: binding.name, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...value });
          continue;
        }
        if (!binding.typeOnly && reviewed.length) {
          values.push({ binding: { local: binding.name, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...moduleValue(nodes, reviewed, binding.name) });
          continue;
        }
        const [node] = nodes;
        // Merged type declarations are one, as `lookup` reads them.
        if (!node || (nodes.length > 1 && !nodes.every(ts.isFunctionDeclaration) && !nodes.every(isTypeDeclaration)))
          throw Error(`TypeScript found ${nodes.length} declarations for ${binding.name}`);
        // A class is a type and, imported as a value, a constructor too.
        if (!binding.typeOnly && nodes.some(n => !ts.isTypeAliasDeclaration(n) && !ts.isInterfaceDeclaration(n))) {
          const guard = node && nodes.length === 1 && ts.isFunctionDeclaration(node) && node.name &&
            isHostFile(node.getSourceFile().fileName) ? bindingGuard(binding) : null;
          // A guard whose runtime function is of another family than its
          // declaration is no guard.
          const entry = guard && node && ts.isFunctionDeclaration(node) && node.name?.text === guard.name &&
            familyOfGuard(guard) === familyOfFile(node.getSourceFile().fileName) ? guard : null;
          const value = valueOf(nodes, binding.name, entry);
          values.push({ binding: { local: binding.name, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...value });
          const forms = value.type.k === "intersection" ? value.type.parts : [value.type];
          const plainForm = forms.find(f => f.k === "function" && f.effect.promise === null);
          const domain = plainForm?.k === "function" ? plainForm.params[0] : undefined;
          if (entry && domain && node && ts.isFunctionDeclaration(node)) {
            const constants = guardConstants(node, entry);
            const tags = entry.tags.map(name => {
              const value = constants.find(c => c.name === name)?.value;
              if (value === undefined) throw Error(`the family's constants hold no ${name}, a tag of ${entry.name}`);
              return value;
            });
            options.hostGuard?.(binding.name, entry, domain,
              entry.kind === "node" ? familyOfGuard(entry).tag.field : null, tags);
          }
        }
        if (!nodes.some(isTypeDeclaration)) continue;
        const declaration = lookup(binding.at, binding.name);
        // An imported alias TypeScript computes from its parameters has no
        // equation, as a local one has none: each application is a computed type.
        if (computedAlias(declaration, aliasOf) || computedMembers(declaration)) continue;
        roots.push({ node: declaration, root: { binding: { kind: "import", local: binding.name,
          imported: binding.imported, specifier: binding.specifier, span: binding.span },
        declaration: identityOf(declaration) } });
      } catch (error) {
        recover(binding.span, error);
        if (!binding.typeOnly && !values.some(v => v.binding.local === binding.name))
          values.push({ binding: { local: binding.name, imported: binding.imported,
            specifier: binding.specifier, span: binding.span },
            declaration: { module: idOf(client), name: binding.name, span: binding.span },
            construct: false, typeParams: [], type: { k: "atom", name: "unknown", span: binding.span } });
      }
    }
    // A call of a namespace member passes the namespace object as the
    // receiver, where a call of the binding it reads passes `undefined`: the
    // two agree for a callee whose contract states no receiver, and the
    // call of one that states its receiver is refused where it is written.
    for (const member of options.namespaceMembers ?? [])
      for (const use of member.uses.filter(u => u.callee)) {
        const name = identifierAt(client, use.name);
        const type = name ? checker.getTypeAtLocation(name) : undefined;
        if (!name || !type) throw new DeclarationError(use.span, "TypeScript types no namespace member here");
        if (checker.getSignaturesOfType(type, SignatureKind.Call).some(s => s.thisParameter !== undefined))
          throw new DeclarationError(use.span, `the call of ${member.local} passes the namespace object as \`this\`, which its declared \`this\` parameter constrains`);
      }
    // The client's ambient declarations (SOURCE-CONTRACTS.md,
    // "Imported, ambient and global values"):
    // each name joins the values like an import of the client's own
    // declaration, at the type it states. Nothing runs them.
    for (const span of options.ambient ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript ambient declaration missing");
      const statement = client.statements.find(s => s.pos <= identifier.pos && identifier.end <= s.end);
      const at: Span = statement ? [statement.getStart(client), statement.end] : span;
      try {
        values.push({ binding: { local: identifier.text, imported: identifier.text, specifier: ambientSpecifier,
          span: at }, ...valueOf(resolveDeclarations(identifier, identifier.text), identifier.text) });
      } catch (error) {
        recover(at, error);
        continue;
      }
    }
    let resolutionContextAt: Span | undefined;
    for (const span of options.locals ?? []) {
      const declaration = client.statements.find(statement =>
        isTypeDeclaration(statement) &&
        statement.getStart(client) === span[0] && statement.end === span[1]);
      if (!declaration || !isTypeDeclaration(declaration) || !declaration.name)
        throw new DeclarationError(span, "TypeScript local declaration missing");
      try {
        const node = lookup(declaration.name, declaration.name.text);
        if (ts.isTypeAliasDeclaration(node) && associatedAlias(node)) {
          resolutionContextAt ??= span;
          options.associatedAlias?.(declaration.name.text, identityOf(node));
          continue;
        }
        // A merged interface's later declarations are the same root. An
        // alias TypeScript computes from its parameters has no equation: each
        // reference to it is a computed type.
        if (roots.some(r => r.node === node) || computedAlias(node, aliasOf) || computedMembers(node)) continue;
        roots.push({ node, root: { binding: { kind: "local", local: declaration.name.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    for (const span of options.globals ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript global reference missing");
      if (roots.some(r => r.root.binding.local === identifier.text)) continue;
      const declaration = targetOf(checker, identifier)?.declarations[0]?.resolve();
      if (!declaration || ts.isTypeParameterDeclaration(declaration) ||
          declaration.getSourceFile().fileName === client.fileName) continue;
      try {
        if (ts.isTypeAliasDeclaration(declaration) && declaration.name.text === "Awaited" &&
            libraryFile(declaration.getSourceFile())) {
          resolutionContextAt ??= span;
          options.awaited?.(span);
          continue;
        }
        if (ts.isTypeAliasDeclaration(declaration) && verifierFile(declaration.getSourceFile()) &&
            declaration.name.text === "Within") {
          options.within?.(span);
          continue;
        }
        if (ts.isTypeAliasDeclaration(declaration) && verifierFile(declaration.getSourceFile()) &&
            (declaration.name.text === "Resolvable" || declaration.name.text === "Awaitable")) {
          resolutionContextAt ??= span;
          if (declaration.name.text === "Resolvable") options.resolvable?.(span);
          else options.awaitable?.(span);
          continue;
        }
        const known = library(identifier, identifier.text);
        if (known) {
          options.library?.(span, known);
          continue;
        }
        const node = lookup(identifier, identifier.text);
        // A global alias TypeScript computes from its parameters, as
        // `Extract` is, has no equation: each application is a computed type.
        if (computedAlias(node, aliasOf) || computedMembers(node)) continue;
        roots.push({ node, root: { binding: { kind: "global", local: identifier.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    // The prototypes' contracts, `Array.prototype`'s and the primitive
    // wrappers', read before the graph is collected so that the library
    // interfaces they name join it.
    // A standard library interface by name, as the overlays name one: its
    // merged declarations, each clean, the first its identity.
    const libraryInterface = (name: string): TypeDeclaration => {
      const symbol = checker.resolveName(name, SymbolFlags.Interface, client, false);
      const parts = (symbol?.declarations ?? []).map(d => d.resolve())
        .filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
      const [first] = parts;
      if (!first || !parts.every(part => libraryFile(part.getSourceFile())))
        throw Error(`the standard library declares no ${name}`);
      for (const part of parts) clean(part, `${idOf(part.getSourceFile())}#${name}`);
      partners.set(first, parts);
      return first;
    };
    // A reference to one, at `args`, from a statement of the overlay of
    // library globals: the interface joins the graph.
    const libraryReference = (name: string, args: TypeTerm[]): TypeTerm => {
      const node = libraryInterface(name);
      valueStarts.push(node);
      const target = identityOf(node);
      return { k: "reference", reference: { name, span: [0, 0], arguments: args.map((): Span => [0, 0]), target },
        args: completeArguments(node, args, null, name), span: [0, 0] };
    };
    const overlayLibrary: OverlayLibrary = {
      symbol: symbolOf,
      wellKnownSymbol: name => {
        const symbol = checker.resolveName("SymbolConstructor", SymbolFlags.Interface, client, false);
        const parts = (symbol?.declarations ?? []).map(d => d.resolve())
          .filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
        // Node may augment SymbolConstructor with unrelated keys. Validate
        // the one declaration whose identity we need, not that whole interface.
        const fields = parts.flatMap(part => part.members)
          .filter(ts.isPropertySignatureDeclaration)
          .filter(p => ts.isIdentifier(p.name) && p.name.text === name);
        const [property, ...more] = fields;
        if (!property) return null;
        if (more.length || !ts.isIdentifier(property.name) ||
            !libraryFile(property.getSourceFile()) ||
            property.getText(property.getSourceFile()).trim() !== `readonly ${name}: unique symbol;`)
          throw Error(`Symbol.${name} is not declared as reviewed`);
        return symbolOf(property.name);
      },
      reference: (node, args, span) => {
        valueStarts.push(node);
        const target = identityOf(node);
        return { k: "reference", reference: { name: target.name, span, arguments: args.map(() => span),
          target }, args: completeArguments(node, args, null, target.name), span };
      },
      libraryFile,
      // The reviewed text as an interface appended to the client, in a probe
      // program of its own, at a name the client does not spell.
      // The declaration read is the one at the appended text's exact start
      // and end, whatever the client declares under any name; only its own
      // syntax is read, so a client declaration merging with it adds nothing.
      reviewed: (body, read) => {
        let index = 0;
        while (client.text.includes(`__TScertReviewed${index}`)) index++;
        const appended = `interface __TScertReviewed${index}${body}`;
        const start = client.text.length + 1;
        return probeProgram(new Map([[client.fileName, `${client.text}\n${appended}\n`]]), program => {
          const file = program.getSourceFile(client.fileName);
          const declaration = file?.statements.find((n): n is InterfaceDeclaration => ts.isInterfaceDeclaration(n) &&
            n.getStart(file) === start && n.end === start + appended.length);
          if (!declaration) throw Error("the reviewed signatures do not parse as the appended interface");
          return read(declaration);
        });
      },
    };
    // The keys a regex's type states (`regexp.mts`): the well-known symbols
    // its methods are keyed by, and the marks, synthetic symbols no source
    // declaration has.
    const markOf = (identity: DeclarationIdentity): number => {
      const key = `mark ${identity.module}#${identity.name}`;
      let index = symbolIndex.get(key);
      if (index === undefined) {
        index = symbols.length;
        symbols.push(identity);
        symbolIndex.set(key, index);
      }
      return index;
    };
    // The native collection iterator a `Set`'s or a `Map`'s members return,
    // its declaration listed with its first use (`array-prototype.mts`).
    const collectionDefinitions: TypeDefinition[] = [];
    const collectionIterator = (element: TypeTerm): TypeTerm => {
      if (!collectionDefinitions.length) collectionDefinitions.push(nativeCollectionIteratorDefinition(
        markOf(collectionIteratorMark), argument => libraryReference("Iterator", [argument])));
      return nativeCollectionIterator(element);
    };
    // Read once; the native match iterator's declaration joins the
    // definitions with them.
    let keysRead: RegExpKeys | undefined;
    const regexpDefinitions: TypeDefinition[] = [];
    const regexpKeys = (): RegExpKeys => {
      if (keysRead) return keysRead;
      const known = (name: string): number => {
        const symbol = overlayLibrary.wellKnownSymbol(name);
        if (symbol === null) throw Error(`the standard library declares no Symbol.${name}, which a regex's methods are keyed by`);
        return symbol;
      };
      keysRead = { match: known("match"), matchAll: known("matchAll"), replace: known("replace"),
        search: known("search"), split: known("split"), matcher: markOf(marks.matcher),
        stringIterator: markOf(marks.stringIterator), iterator: element => libraryReference("Iterator", [element]) };
      return keysRead;
    };
    // The native match iterator's declaration, which names the library's
    // `Iterator`: listed where a native regex or its iteration is, before
    // the graph is collected.
    const nativeMatches = (): RegExpKeys => {
      const keys = regexpKeys();
      if (!regexpDefinitions.length) regexpDefinitions.push(nativeIteratorDefinition(keys));
      return keys;
    };
    // A primitive's members are read through its wrapper's prototype: its
    // contract joins the definitions, and the built-in prototype the values,
    // an assumption at that contract as an import is at its type. A string's
    // `split` gives an array, whose members the array prototype states.
    const primitiveProtos: TypeDefinition[] = [];
    const primitives = new Map<PrimitiveKind, Span>();
    let stringSplit: Span | undefined;
    for (const span of options.memberReceivers ?? []) {
      const receiver = expressionAt(client, span);
      if (!receiver) throw new DeclarationError(span, "TypeScript member receiver missing");
      const type = checker.getTypeAtLocation(receiver);
      const kinds = type ? primitivesOf(type) : [];
      for (const kind of kinds)
        if (!primitives.has(kind)) primitives.set(kind, span);
      const member = receiver.parent;
      if (kinds.includes("string") && member && ts.isPropertyAccessExpression(member) &&
          member.name.text === "split" && member.parent && ts.isCallExpression(member.parent))
        stringSplit ??= span;
    }
    // Every object's prototype chain ends at `Object.prototype`, and every
    // function's holds `Function.prototype`: a declaration merging a member
    // into either interface states it of every such value, which no unit
    // reads at the standard library's contract (`mergeRefusal`).
    for (const name of ["Object", "Function"]) {
      const parts = (checker.resolveName(name, SymbolFlags.Interface, client, false)?.declarations ?? [])
        .map(d => d.resolve()).filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
      const { refusal } = mergeRefusal(checker, libraryFile, parts, overlayLibrary.reviewed);
      if (refusal) throw new DeclarationError(options.root ?? [0, 0], mergeMessage(name, refusal));
    }
    let arrayProto: TypeDefinition[] = [];
    const arraysAt = options.arrays ?? stringSplit;
    if (arraysAt) {
      try {
        arrayProto = arrayPrototype(checker, client, overlayLibrary, options.arrayOverlay ?? overlay);
      } catch (error) {
        throw new DeclarationError(arraysAt, messageOf(error), error);
      }
    }
    for (const [kind, at] of primitives) {
      try {
        const definition = primitivePrototype(checker, client, overlayLibrary, kind, splitSeparators(client));
        primitiveProtos.push(definition);
        const name = primitivePrototypeName(kind);
        values.push({ binding: { local: name, imported: name, specifier: prototypeSpecifier, span: at },
          declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: definition.declaration.name, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        recover(at, error);
        continue;
      }
    }
    // A `for...of` over a host iterable other than an array steps the
    // iteration intrinsic of its kind, picked by TypeScript's type of the
    // iterable, every part of a union alike; an object with a
    // `[Symbol.iterator]` of none of these kinds is a program's iterable,
    // which runs the iterator protocol (`protocolForOf` in the parser).
    const collections: Record<string, string> = { Set: iterateSetName, Map: iterateMapName,
      SetIterator: iterateIteratorName, MapIterator: iterateIteratorName,
      RegExpStringIterator: iterateRegExpStringName };
    const iterationKind = (part: Type): string => {
      if (checker.isArrayType(part) || checker.isTupleType(part)) return "array";
      if (part.flags & TypeFlags.StringLike) return iterateStringName;
      const symbol = part.getSymbol();
      const named = symbol && Object.hasOwn(collections, symbol.name) ? collections[symbol.name] : undefined;
      const library = !!symbol?.declarations.length &&
        symbol.declarations.every(d => libraryFile(d.resolve()?.getSourceFile() ?? client));
      if (named && library) return named;
      // A match array is an array (`regexp.mts` reads `RegExpExecArray` and
      // `RegExpMatchArray` as tuple views), which the host builds with
      // `ArrayCreate`: iterated as one.
      if (library && (symbol?.name === "RegExpExecArray" || symbol?.name === "RegExpMatchArray")) return "array";
      // A compiler-API node list is read as a dense readonly array of its
      // elements (COMPILER-API.md, "Node lists in the model"): its own
      // `Symbol.iterator`, indexing and `Array.from` agree (T4, run by C4),
      // so it is iterated as that array is, a host assumption about the
      // package's values.
      if (nodeListType(part)) return "array";
      if (part.flags & TypeFlags.Object) {
        const method = checker.getPropertiesOfType(part).find(p => p.name.startsWith("__@iterator@"));
        if (method) {
          // A program's iterable runs the iterator protocol, whose early exit
          // calls the iterator's `return`: the iterator's type must state it
          // (optional or not) for that call to have a contract.
          const methodType = checker.getTypeOfSymbol(method);
          const iterators = methodType ? checker.getSignaturesOfType(methodType, SignatureKind.Call)
            .map(s => checker.getReturnTypeOfSignature(s)) : [];
          const returns = iterators.flatMap(t => !t ? [undefined]
            : (isUnionType(t) ? t.getTypes() : [t]).map(i => checker.getPropertyOfType(i, "return")));
          const closable = returns.length > 0 && returns.every(r => !!r);
          // A `return` every iterator declares a required method is a method
          // member, read bound to its host; any other (an optional method, a
          // property) a property the close reads and tests.
          const bound = closable && returns.every(r => !!r && r.declarations.length > 0 &&
            r.declarations.every(d => {
              const node = d.resolve();
              return !!node && ((ts.isMethodSignatureDeclaration(node) && !node.postfixToken) ||
                (ts.isMethodDeclaration(node) && !node.postfixToken));
            }));
          // The protocol reads the member by its key, the well-known symbol
          // its declaration's computed name spells: it joins the symbols.
          for (const declaration of method.declarations) {
            const node = declaration.resolve();
            const name = node && nameOf(node);
            if (name && ts.isComputedPropertyName(name) && (ts.isIdentifier(name.expression) ||
                ts.isPropertyAccessExpression(name.expression))) {
              iteratorSymbol = symbolOf(name.expression);
              break;
            }
          }
          return !closable ? "client-unclosable" : bound ? "client-method" : "client";
        }
      }
      return "other";
    };
    let iteratorSymbol: number | null = null;
    const listedIterations = new Set<string>();
    const iterated = [...(options.iterables ?? []).map(span => ({ span, spread: false })),
      ...(options.spreads ?? []).map(span => ({ span, spread: true }))];
    for (const { span, spread } of iterated) {
      const iterable = expressionAt(client, span);
      if (!iterable) throw new DeclarationError(span, "TypeScript iterable missing");
      // The iterable's type, read part by part: a failure of the compiler's
      // API there is located at the iterable.
      const kindsOf = (): string[] => {
        const type = checker.getTypeAtLocation(iterable);
        return [...new Set((type && isUnionType(type) ? type.getTypes() : type ? [type] : []).map(iterationKind))];
      };
      let kinds: string[];
      try {
        kinds = kindsOf();
      } catch (error) {
        recover(span, error);
        continue;
      }
      const [kind] = kinds;
      // A union with a program's iterable among its parts runs the protocol
      // (`client`), which every part's own iterator answers.
      const picked = kinds.length === 1 && kind ? kind : kinds.includes("client-unclosable") ? "client-unclosable"
        : kinds.includes("client") ? "client" : kinds.includes("client-method") ? "client-method" : "other";
      if (picked === "array" || picked === "other") continue;
      const program = picked.startsWith("client");
      const listed = spread && !program ? spreadName(picked) : picked;
      if (!program && !listedIterations.has(listed)) {
        listedIterations.add(listed);
        try {
          const intrinsic = iterationIntrinsic(listed, (name, args) => libraryReference(name, args),
            element => { nativeMatches(); return nativeIterator(element); }, collectionIterator);
          values.push({ binding: { local: intrinsic.name, imported: intrinsic.name,
            specifier: intrinsicModule, span },
            declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
            construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
        } catch (error) {
          recover(span, error);
          continue;
        }
      }
      options.iterable?.(span, listed, program ? iteratorSymbol : null);
    }
    // An array pattern's rest over what is no one tuple of required
    // positions (an array, a union of tuples, a tuple with optional or rest
    // elements) is a slice, which `%RestFrom:k%` collects.
    const listedRests = new Set<number>();
    for (const { span, index } of options.restTargets ?? []) {
      const target = expressionAt(client, span);
      if (!target) throw new DeclarationError(span, "TypeScript rest source missing");
      const type = checker.getTypeAtLocation(target);
      const tuple = type && !isUnionType(type) && checker.isTupleType(type) && isTypeReference(type)
        ? type.getTarget() : undefined;
      const fixed = !!tuple && isTupleType(tuple) && (tuple.elementFlags ?? []).every(f => f === ElementFlags.Required);
      if (fixed) continue;
      if (!listedRests.has(index)) {
        listedRests.add(index);
        const intrinsic = restFromIntrinsic(index);
        values.push({ binding: { local: intrinsic.name, imported: intrinsic.name, specifier: intrinsicModule, span },
          declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
          construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
      }
      options.restSlice?.(span);
    }
    // `async`, `await` and `for...of`, as the intrinsics that stand for them
    // (`intrinsics.mts`): trusted steps at their signatures, listed as values
    // like an import's.
    // Listed once, located at the first construct or overlay entry that uses
    // them.
    const intrinsicsListed = new Set<string>();
    // Resolve Promise only if a requested intrinsic, or a resolution
    // descriptor, actually names it.
    const promiseType = (argument: TypeTerm): TypeTerm => {
      const symbol = checker.resolveName("Promise", SymbolFlags.Interface, client, false);
      const parts = (symbol?.declarations ?? []).map(d => d.resolve())
        .filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
      const [promise] = parts;
      if (!promise) throw Error("the standard library declares no Promise");
      for (const part of parts) clean(part, `${idOf(part.getSourceFile())}#Promise`);
      partners.set(promise, parts);
      if (!valueStarts.includes(promise)) valueStarts.push(promise);
      return { k: "reference", reference: { name: "Promise", span: [0, 0],
        arguments: [[0, 0]], target: identityOf(promise) }, args: [argument], span: [0, 0] };
    };
    // A resolution descriptor is relative to the stable family `%Stable%`
    // and the native `Promise`: listed once, where the first descriptor is.
    let stableListed = false;
    const listStable = (at: Span): void => {
      if (stableListed) return;
      try { promiseType({ k: "atom", name: "unknown", span: [0, 0] }); }
      catch (error) { throw new DeclarationError(at, messageOf(error), error); }
      stableListed = true;
    };
    const listIntrinsics = (at: Span, names: string[]): void => {
      const needed = new Set(names.filter(name => !intrinsicsListed.has(name)));
      if (!needed.size) return;
      if ([...needed].some(name => resolutionIntrinsics.includes(name))) listStable(at);
      try {
        for (const intrinsic of intrinsics(promiseType, needed))
          values.push({ binding: { local: intrinsic.name, imported: intrinsic.name,
            specifier: intrinsicModule, span: at },
            declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
            construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
        for (const name of needed) intrinsicsListed.add(name);
      } catch (error) {
        recover(at, error);
      }
    };
    if (options.intrinsics) listIntrinsics(options.intrinsics.span, options.intrinsics.names);
    for (const span of assertionSpans) listIntrinsics(span, [assertionFailureName]);
    if (resolutionContextAt) listStable(resolutionContextAt);
    // `k in o` with a key TypeScript types as string literals only is the
    // model's key test, which narrows `o`; any other key, a number, a symbol
    // or a string known only at run time, is the host's `%HasProperty%`.
    for (const span of options.inKeys ?? []) {
      const key = expressionAt(client, span);
      if (!key) throw new DeclarationError(span, "TypeScript `in` key missing");
      const type = checker.getTypeAtLocation(key);
      const parts = type && isUnionType(type) ? type.getTypes() : type ? [type] : [];
      if (parts.length && parts.every(t => !!(t.flags & TypeFlags.StringLiteral))) continue;
      listIntrinsics(span, [hasPropertyName]);
      options.hostIn?.(span);
    }
    for (const span of options.elementReads ?? []) {
      const read = expressionAt(client, span);
      if (!read || !ts.isElementAccessExpression(read)) throw new DeclarationError(span, "TypeScript element read missing");
      const object = checker.getTypeAtLocation(read.expression);
      const key = checker.getTypeAtLocation(read.argumentExpression);
      const objects = object && isUnionType(object) ? object.getTypes() : object ? [object] : [];
      const keys = key && isUnionType(key) ? key.getTypes() : key ? [key] : [];
      if (objects.length && objects.every(t => checker.isArrayType(t) || checker.isTupleType(t) || nodeListType(t)) &&
          keys.length && keys.every(t => !!(t.flags & TypeFlags.Number))) {
        listIntrinsics(span, [elementAtName]);
        options.hostElement?.(span);
      }
    }
    // A regular expression literal is a call of the intrinsic of its shape,
    // listed once per shape at the first literal of it.
    for (const span of options.regexps ?? []) {
      const literal = expressionAt(client, span);
      if (!literal || literal.kind !== ts.SyntaxKind.RegularExpressionLiteral)
        throw new DeclarationError(span, "TypeScript regular expression literal missing");
      const { pattern, flags } = literalParts(literal.getText(client));
      const shape = regexpShape(pattern, flags);
      const name = regexpIntrinsicName(shape);
      if (!intrinsicsListed.has(name)) {
        try {
          values.push({ binding: { local: name, imported: name, specifier: intrinsicModule, span },
            declaration: { module: intrinsicModule, name, span: [0, 0] }, construct: false, typeParams: [],
            // Evaluating a literal allocates the regex and runs no code. Its
            // footprint is empty and its result fresh: every own location of
            // the regex, `lastIndex` its only mutable one, is allocated by
            // this evaluation (SOURCE-CONTRACTS.md, "Native footprints").
            type: { k: "function", effect: emptyEffect, receiver: null, params: [], rest: null,
              result: nativeRegExp(shape, nativeMatches()), span: [0, 0] } });
        } catch (error) {
          recover(span, error);
          continue;
        }
        intrinsicsListed.add(name);
      }
      options.regexp?.(span, name);
    }
    for (const span of options.dispatchCalls ?? []) {
      const call = expressionAt(client, span);
      if (!call || !ts.isCallExpression(call) || !ts.isPropertyAccessExpression(call.expression))
        throw new DeclarationError(span, "TypeScript string method call missing");
      const method = call.expression.name.text;
      const [argument] = call.arguments;
      if (!isDispatchMethod(method) || !argument) continue;
      const partsOf = (type: Type | undefined): readonly Type[] => type && isUnionType(type) ? type.getTypes() : type ? [type] : [];
      const receivers = partsOf(checker.getTypeAtLocation(call.expression.expression));
      const objects = partsOf(checker.getTypeAtLocation(argument));
      if (!receivers.length || !receivers.every(t => !!(t.flags & TypeFlags.StringLike)) ||
          !objects.length || !objects.every(t => !!(t.flags & (TypeFlags.Object | TypeFlags.NonPrimitive | TypeFlags.Intersection))))
        continue;
      const name = dispatchName(method);
      if (!intrinsicsListed.has(name)) {
        try {
          const intrinsic = dispatchIntrinsic(method, regexpKeys());
          values.push({ binding: { local: name, imported: name, specifier: intrinsicModule, span },
            declaration: { module: intrinsicModule, name, span: [0, 0] }, construct: false,
            typeParams: intrinsic.typeParams, type: intrinsic.type });
        } catch (error) {
          recover(span, error);
          continue;
        }
        intrinsicsListed.add(name);
      }
      options.dispatch?.(span, name);
    }
    for (const span of options.libraryNames ?? []) {
      const name = identifierAt(client, span);
      if (!name) continue;
      // A member name is the property its object's type has under it; any
      // other name the declaration it is bound to.
      const access = name.parent;
      const object = access && ts.isPropertyAccessExpression(access) && access.name === name
        ? checker.getTypeAtLocation(access.expression) : undefined;
      const symbol = access && ts.isPropertyAccessExpression(access) && access.name === name
        ? object && checker.getPropertyOfType(object, name.text) : checker.getSymbolAtLocation(name);
      if (!symbol || symbol.flags & SymbolFlags.Alias || !symbol.declarations.length) continue;
      if (symbol.declarations.every(d => {
        const node = d.resolve();
        return !!node && libraryFile(node.getSourceFile());
      })) options.libraryName?.(span);
    }
    for (const span of options.libraryValues ?? []) {
      const name = identifierAt(client, span);
      const symbol = name && checker.getSymbolAtLocation(name);
      if (!symbol || symbol.flags & SymbolFlags.Alias || !symbol.declarations.length) continue;
      // An interface or a type merged with the value declares no value.
      const values = symbol.declarations.map(d => d.resolve())
        .filter(node => !node || !(ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)));
      if (values.length && values.every(node => {
        if (!node || !libraryFile(node.getSourceFile())) return false;
        if (ts.isFunctionDeclaration(node)) return true;
        const list = node.parent;
        return ts.isVariableDeclaration(node) && !!list && ts.isVariableDeclarationList(list) &&
          !(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const));
      })) options.libraryValue?.(span);
    }
    for (const span of options.receiverTargets ?? []) {
      const name = identifierAt(client, span);
      const symbol = name && checker.getSymbolAtLocation(name);
      if (symbol && symbol.flags & SymbolFlags.Method) options.methodTarget?.(span);
    }
    // Global variables the client reads, such as Node's `process` (SOURCE-CONTRACTS.md,
    // "Imported, ambient and global values"): each joins the values like an import, at a definition
    // of its own, keyed by the variable's declaration, that holds only the
    // members and call signatures the client's references select.
    const selections: TypeDefinition[] = [];
    const groups = new Map<number, Identifier[]>();
    for (const span of options.globalValues ?? []) {
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript global value reference missing");
      const symbol = checker.getSymbolAtLocation(identifier);
      if (!symbol || symbol.flags & SymbolFlags.Alias || checker.isUnknownSymbol(symbol) ||
          checker.isUndefinedSymbol(symbol) || !symbol.declarations.length) continue;
      const nodes = symbol.declarations.map(d => d.resolve());
      if (nodes.some(n => !n || n.getSourceFile().fileName === client.fileName)) continue;
      const group = groups.get(symbol.id);
      if (group) group.push(identifier);
      else groups.set(symbol.id, [identifier]);
    }
    for (const uses of groups.values()) {
      const [first] = uses;
      if (!first) continue;
      const at: Span = [first.getStart(client), first.end];
      try {
        const selection = selectGlobal(checker, uses, { lookup, identityOf: idOf, libraryFile, clean, valueScope, partners,
          overlay: globalsOverlay, test: (span, test) => options.globalTest?.(span, test),
          intrinsic: (span, name) => {
            listIntrinsics(span, [name]);
            options.globalIntrinsic?.(span, name);
          },
          construct: span => options.globalConstruct?.(span),
          library: libraryReference,
          define: definition => {
            const key = (d: TypeDefinition) => `${d.declaration.module}#${d.declaration.name}`;
            if (!selections.some(d => key(d) === key(definition))) selections.push(definition);
          } });
        if (!selection) continue;
        const binding = { local: first.text, imported: first.text, specifier: globalSpecifier, span: at };
        // A global only constructed is its construct signatures, as a class
        // value is; any other is its selection.
        if (selection.construct !== undefined) {
          values.push({ binding, construct: true, ...selection.construct });
          continue;
        }
        const definition = selection.definition;
        selections.push(definition);
        values.push({ binding, declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: first.text, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        recover(at, error);
        continue;
      }
    }
    // A private name reads the key of the member TypeScript binds it to.
    for (const span of options.privateNames ?? []) {
      const name = expressionAt(client, span);
      if (!name || !ts.isPrivateIdentifier(name)) throw new DeclarationError(span, "TypeScript private name missing");
      try {
        options.privateName?.(span, privateNameOf(name));
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    // An element key naming a `unique symbol` constant reads that symbol's
    // key; any other is an ordinary index, left to the expression.
    for (const span of options.symbolKeys ?? []) {
      // `S.k`: a readonly `unique symbol` property, such as the well-known
      // `Symbol.iterator`.
      const access = expressionAt(client, span);
      if (access && ts.isPropertyAccessExpression(access) && ts.isIdentifier(access.name)) {
        const members = targetOf(checker, access.name)?.declarations.map(d => d.resolve()) ?? [];
        const [member] = members;
        if (members.length !== 1 || !member || !ts.isPropertySignatureDeclaration(member) || !member.type ||
            !ts.isTypeOperatorNode(member.type) || member.type.operator !== ts.SyntaxKind.UniqueKeyword)
          continue;
        try {
          options.symbolKey?.(span, symbolOf(access));
        } catch (error) {
          recover(span, error);
          continue;
        }
        continue;
      }
      const identifier = identifierAt(client, span);
      if (!identifier) throw new DeclarationError(span, "TypeScript element key missing");
      const nodes = targetOf(checker, identifier)?.declarations.map(d => d.resolve()) ?? [];
      const [node] = nodes;
      if (nodes.length !== 1 || !node || !ts.isVariableDeclaration(node) || !node.type ||
          !ts.isTypeOperatorNode(node.type) || node.type.operator !== ts.SyntaxKind.UniqueKeyword)
        continue;
      try {
        options.symbolKey?.(span, symbolOf(identifier));
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    for (const span of options.staticReads ?? []) {
      const name = identifierAt(client, span);
      const access = name?.parent;
      if (!name || !access || !ts.isPropertyAccessExpression(access) || !ts.isIdentifier(access.expression))
        throw new DeclarationError(span, "TypeScript member read missing");
      const members = targetOf(checker, name)?.declarations.map(d => d.resolve()) ?? [];
      const owners = targetOf(checker, access.expression)?.declarations.map(d => d.resolve()) ?? [];
      const [member] = members, [owner] = owners;
      if (members.length === 1 && owners.length === 1 && member && owner &&
          ts.isClassDeclaration(owner) && owner.name && owner.parent === client && member.parent === owner &&
          (ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) &&
          member.modifiers?.some(m => m.kind === ts.SyntaxKind.StaticKeyword))
        options.staticMember?.(span, owner.name.text);
      else if (members.length === 1 && owners.length === 1 && member && owner &&
          ts.isClassDeclaration(owner) && member.parent !== owner && ts.isClassDeclaration(member.parent) &&
          (ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) &&
          member.modifiers?.some(m => m.kind === ts.SyntaxKind.StaticKeyword))
        options.inheritedStatic?.(span);
    }
    for (const span of options.classTests ?? []) {
      const name = identifierAt(client, span);
      if (!name) throw new DeclarationError(span, "TypeScript `instanceof` operand missing");
      const owners = targetOf(checker, name)?.declarations.map(d => d.resolve()) ?? [];
      const [owner] = owners;
      if (owners.length === 1 && owner && ts.isClassDeclaration(owner) && owner.name &&
          owner.parent === client && owner.name.text === name.text)
        options.classTest?.(span, owner.name.text);
    }
    for (const span of options.hookTests ?? []) {
      const name = identifierAt(client, span);
      if (!name) throw new DeclarationError(span, "TypeScript `instanceof` operand missing");
      const type = checker.getTypeAtLocation(name);
      const hook = type ? checker.getPropertiesOfType(type).find(p => p.name.startsWith("__@hasInstance@")) : undefined;
      // A hook the program's types state, not the one `Function.prototype`
      // holds, which a function value inherits rather than owns.
      const declaration = hook?.declarations[0]?.resolve();
      if (!declaration || libraryFile(declaration.getSourceFile() ?? client)) continue;
      const key = declaration ? nameOf(declaration) : undefined;
      const target = key && ts.isComputedPropertyName(key) && ts.isPropertyAccessExpression(key.expression) &&
        ts.isIdentifier(key.expression.name) ? targetOf(checker, key.expression.name) : undefined;
      if (target?.declarations.some(d => libraryFile(d.resolve()?.getSourceFile() ?? client)))
        options.hookTest?.(span);
    }
    for (const span of options.bindingReads ?? []) {
      const name = identifierAt(client, span);
      if (!name) throw new DeclarationError(span, "TypeScript binding reference missing");
      const parent = name.parent;
      const symbol = parent && ts.isShorthandPropertyAssignment(parent) && parent.name === name
        ? checker.getShorthandAssignmentValueSymbol(parent) : checker.getSymbolAtLocation(name);
      const declarations = symbol?.declarations.map(d => d.resolve()) ?? [];
      const [declaration] = declarations;
      const declared = declaration && nameOf(declaration);
      if (declarations.length === 1 && declaration && declared && ts.isIdentifier(declared) &&
          declaration.getSourceFile().fileName === client.fileName)
        options.bindingRead?.(span, [declared.getStart(client), declared.end]);
    }
    // A closure parameter without a type is at the type TypeScript gives it
    // from its context: a source type term whose names enter the same
    // declaration graph as written references.
    const contextualStarts: { node: TypeDeclaration; span: Span }[] = [];
    const contextualTerm = (type: Type, span: Span): TypeTerm => {
      const term = readContextualTerm(type, span);
      validateAnnotation(term, (_span, message) => { throw Error(message); });
      return term;
    };
    // An enum member's literal type, `E.M` (SyntaxKind.AbstractKeyword): its
    // value as the enum's interpretation computes it (`enumMembersOf`), a
    // host enum only where the compiler-API contract lists it.
    const contextualEnumMember = (type: Type, span: Span): TypeTerm | null => {
      if (!(type.flags & TypeFlags.EnumLiteral) || type.isUnionType()) return null;
      const member = type.getSymbol()?.declarations[0]?.resolve();
      const owner = member?.parent;
      if (!member || !ts.isEnumMember(member) || !owner || !ts.isEnumDeclaration(owner))
        throw Error(`the contextual enum literal ${checker.typeToString(type)} names no enum member`);
      const name = owner.name.text;
      if (isHostFile(owner.getSourceFile().fileName) && !readableHostEnum([owner], name, null))
        throw Error(`the host enum ${name} is not one the compiler-API contract reads (compiler-api.mts), nor a family's tag enum its runtime object matches`);
      const value = enumMembersOf([owner], name)[owner.members.indexOf(member)]?.value;
      if (value === undefined)
        throw Error(`the enum member ${name}.${member.name.getText(owner.getSourceFile())} has no value TypeScript computes, so no literal type`);
      return literalTerm(value, span);
    };
    // An anonymous record (an object literal's type, a type literal, a mapped
    // type's instance such as `Record<string, unknown>`): the object contract
    // its members state. A type literal or mapped type the program writes is
    // read as written, by the annotation reader, where TypeScript gives it
    // outside any generic declaration or at its declaration's own binders.
    // Any other (an object literal's type, a library mapped type's instance,
    // a generic declaration's record at an instance) is read member by
    // member: a member of its own type literal at its written modifiers, and
    // at its written type where that names no binder; any other at the type
    // TypeScript instantiates, readonly where the instantiation makes it so.
    // An optional member at an instantiated type is refused, save an object
    // literal's at `undefined`: the compiler's API gives an anonymous record
    // no instantiation of its declaration's binders, and the instantiated
    // type carries the `undefined` optionality adds. Each index signature is
    // read at its key's kind and capability. A member no object contract
    // states (a method, an accessor, a symbol key, an index
    // of another key) is refused.
    const contextualRecord = (type: Type, span: Span): TypeTerm | null => {
      if (!(type.flags & TypeFlags.Object)) return null;
      const declarations = (type.getSymbol()?.declarations ?? []).map(d => d.resolve());
      if (!declarations.length || !declarations.every(d => !!d &&
          (ts.isTypeLiteralNode(d) || ts.isObjectLiteralExpression(d) || ts.isMappedTypeNode(d)))) return null;
      const text = checker.typeToString(type);
      const [only] = declarations;
      if (declarations.length === 1 && only && (ts.isTypeLiteralNode(only) || ts.isMappedTypeNode(only)) &&
          !libraryFile(only.getSourceFile())) {
        const binders = enclosingBinders(only);
        if (!binders.length || checker.getTypeFromTypeNode(only)?.id === type.id)
          return computedContext.annotation(only, only, binders);
      }
      if (checker.getSignaturesOfType(type, SignatureKind.Call).length ||
          checker.getSignaturesOfType(type, SignatureKind.Construct).length)
        throw Error(`the contextual record ${text} is callable, which an annotation states`);
      const fields = checker.getPropertiesOfType(type).map(p => {
        const declaration = p.declarations[0]?.resolve();
        if (p.name.startsWith("__@") || (declaration && (ts.isMethodSignatureDeclaration(declaration) ||
            ts.isMethodDeclaration(declaration) || ts.isGetAccessorDeclaration(declaration) ||
            ts.isSetAccessorDeclaration(declaration))))
          throw Error(`the contextual record ${text} has a member ${p.name} no object contract states (a method, an accessor or a symbol key), which an annotation states`);
        const member = checker.getTypeOfSymbol(p);
        if (!member) throw Error(`TypeScript gives the member ${p.name} of ${text} no type`);
        const optional = (p.flags & SymbolFlags.Optional) !== 0;
        // A member of the record's own type literal is described by its
        // syntax: its modifiers, and its written type where that names
        // none of the literal's binders, read as the annotation reader
        // reads it. A mapped type's member keeps its originating property
        // as declaration, which describes it no more: it, and an object
        // literal's, is the member TypeScript instantiates, readonly where
        // the instantiation makes it so (`checkFlags & 8`).
        const own = !!declaration && !!only && ts.isTypeLiteralNode(only) && declaration.parent === only &&
          (ts.isPropertySignatureDeclaration(declaration) || ts.isPropertyDeclaration(declaration));
        const node = own && declaration && (ts.isPropertySignatureDeclaration(declaration) ||
          ts.isPropertyDeclaration(declaration)) ? declaration.type : undefined;
        const binders = declaration ? enclosingBinders(declaration) : [];
        const mentions = (n: Node): boolean => (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) &&
          binders.includes(n.typeName.text)) || (n.forEachChild(c => mentions(c) || undefined) ?? false);
        const writtenType = !!node && !!declaration && !libraryFile(declaration.getSourceFile()) && !mentions(node);
        // An optional member's present value is its written type; where
        // TypeScript gives only the type it reads, with the `undefined`
        // optionality adds, the written contract is not recovered, save
        // for an object literal's member at `undefined` alone (an array
        // literal's records, each given the others' members so).
        const literalMember = !!declaration && (ts.isPropertyAssignment(declaration) ||
          ts.isShorthandPropertyAssignment(declaration));
        if (optional && !writtenType &&
            !(literalMember && member.flags & TypeFlags.Undefined && !member.isUnionType()))
          throw Error(`the contextual record ${text} is an instance of an anonymous record, whose instantiation the compiler's API does not give, and its optional member ${p.name} is at a type with the \`undefined\` optionality adds, from which its written contract is not recovered; an annotation states it`);
        const memberType = writtenType && node && declaration
          ? computedContext.annotation(node, declaration, binders) : contextualTerm(member, span);
        const readonly = own
          ? !!declaration && childrenOf(declaration, "modifiers").some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword)
          : (p.checkFlags & 8) !== 0;
        return { name: p.name, optional, readonly, type: memberType, span };
      });
      let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
      let numberIndex: Extract<TypeTerm, { k: "object" }>["numberIndex"];
      let symbolIndex: Extract<TypeTerm, { k: "object" }>["symbolIndex"];
      for (const info of checker.getIndexInfosOfType(type)) {
        const index = { readonly: info.isReadonly, value: contextualTerm(info.valueType, span), span };
        const key = info.keyType.flags;
        if (key & TypeFlags.String) stringIndex = index;
        else if (key & TypeFlags.Number) numberIndex = index;
        else if (key & TypeFlags.ESSymbol) symbolIndex = index;
        else throw Error(`the contextual record ${text} has an index of key ${checker.typeToString(info.keyType)}, which an annotation states`);
      }
      return { k: "object", fields, stringIndex, ...(numberIndex ? { numberIndex } : {}),
        ...(symbolIndex ? { symbolIndex } : {}), calls: [], span };
    };
    // A function's type (SOURCE-ELABORATION.md, "Source closures and their
    // annotations"): a function type or callable type literal the program
    // writes is read as written by the annotation reader, where TypeScript
    // gives it outside any generic declaration or at its declaration's own
    // binders, as a record's type literal is. Any other callable without members (a generic declaration's
    // callable at an instance, a library's, a function's `typeof`) is
    // read through its one call signature as TypeScript instantiates it: its
    // receiver, each parameter at its type (an optional or defaulted one's
    // with the `undefined` that admits), a rest at its array's element or
    // its tuple's positions, its result, and a guard's or an assertion's
    // promise about a parameter as a second form, with the ordinary effect
    // an annotation of it states. Refused, as no contract the reading
    // recovers: type parameters, a promise about the receiver or without a
    // type, a rest of another type, a construct signature, a second
    // signature, a member beside the call signature.
    const contextualCallable = (type: Type, span: Span): TypeTerm | null => {
      if (!(type.flags & TypeFlags.Object)) return null;
      const calls = checker.getSignaturesOfType(type, SignatureKind.Call);
      if (!calls.length) return null;
      const declarations = (type.getSymbol()?.declarations ?? []).map(d => d.resolve());
      const [only, ...others] = declarations;
      const text = checker.typeToString(type);
      if (only && !others.length && (ts.isFunctionTypeNode(only) || ts.isTypeLiteralNode(only)) &&
          !libraryFile(only.getSourceFile())) {
        const binders = enclosingBinders(only);
        if (!binders.length || checker.getTypeFromTypeNode(only)?.id === type.id)
          return computedContext.annotation(only, only, binders);
      }
      const refuse = (what: string): never => {
        throw Error(`TypeScript types this unannotated closure parameter from its context as ${text}, ${what}, which an annotation states`);
      };
      const [signature, ...more] = calls;
      if (!signature || more.length || checker.getSignaturesOfType(type, SignatureKind.Construct).length)
        return refuse("not one call signature");
      if (checker.getPropertiesOfType(type).length || checker.getIndexInfosOfType(type).length)
        return refuse("a callable with members");
      if (signature.getTypeParameters().length) return refuse("a generic signature");
      const self = signature.getThisParameter();
      const selfType = self && checker.getTypeOfSymbol(self);
      if (self && !selfType) return refuse("a signature whose receiver has no type");
      const receiver = selfType ? contextualTerm(selfType, span) : null;
      const parameters = signature.getParameters();
      const params: TypeTerm[] = [];
      let rest: TypeTerm | null = null;
      for (const [index, p] of parameters.entries()) {
        const declaration = p.declarations[0]?.resolve();
        // The signature gives the argument contract, including `undefined`
        // for a defaulted parameter. For a rest it gives one position's
        // type; its symbol gives the aggregate array or tuple to expand.
        const parameter = declaration && ts.isParameterDeclaration(declaration) && declaration.dotDotDotToken
          ? checker.getTypeOfSymbol(p) : checker.getParameterType(signature, index);
        if (p.declarations.length !== 1 || !declaration || !ts.isParameterDeclaration(declaration) || !parameter)
          return refuse("a signature with a parameter no declaration states");
        const term = contextualTerm(parameter, span);
        if (!declaration.dotDotDotToken) {
          params.push(term);
          continue;
        }
        const positions = index === parameters.length - 1
          ? restPositions(restTerm(valueScope(declaration, text), term)) : null;
        if (!positions) return refuse("a signature with a rest that is not an array or a tuple of required positions");
        if (positions.k === "positions") params.push(...positions.positions);
        else rest = positions.element;
      }
      const returned = checker.getReturnTypeOfSignature(signature);
      if (!returned) return refuse("a signature of no result type");
      const plain: FunctionTerm = { k: "function", effect: ordinaryEffect, receiver, params, rest,
        result: contextualTerm(returned, span), span };
      const predicate = checker.getTypePredicateOfSignature(signature);
      if (!predicate) return plain;
      const asserts = predicate.kind === TypePredicateKind.AssertsIdentifier;
      const about = predicate.parameterIndex;
      const declared = about === undefined ? undefined : parameters[about]?.declarations[0]?.resolve();
      if (!(asserts || predicate.kind === TypePredicateKind.Identifier) || about === undefined || !predicate.type ||
          !declared || !ts.isParameterDeclaration(declared) || declared.dotDotDotToken)
        return refuse("a promise about the receiver, a rest or no type");
      return oneTerm([plain, { ...plain, effect: promiseEffect(asserts, about),
        result: contextualTerm(predicate.type, span) }], span);
    };
    const typesRead = new Set<number>();
    const readContextualTerm = (type: Type, span: Span): TypeTerm => {
      if (type.flags & TypeFlags.Any)
        throw Error("TypeScript types this unannotated closure parameter from its context as `any`, which states no contract");
      const member = contextualEnumMember(type, span);
      if (member) return member;
      const literals = literalUnion(type, span);
      if (literals) return literals;
      const text = () => checker.typeToString(type);
      // A declaration by name is read as a reference, which closes a
      // recursive type at its name; any other type through its structure.
      // A type reached again while it is being read contains itself through
      // a structure no declaration names, which only an annotation states.
      if (typesRead.has(type.id))
        throw Error(`the contextual type ${text()} contains itself through a structure no declaration names, which an annotation states`);
      typesRead.add(type.id);
      try {
        const symbol = type.getAliasSymbol() ?? type.getSymbol();
        const nodes = (symbol?.declarations ?? []).map(d => d.resolve());
        const [node] = nodes;
        if (nodes.length === 1 && node && isTypeDeclaration(node) && node.name && !libraryFile(node.getSourceFile())) {
          if (ts.isClassDeclaration(node) && !isInstanceReference(type))
            throw Error(`the contextual type ${text()} is a class constructor, not an instance type`);
          // An alias's own arguments, none for an alias without parameters
          // (`type AbstractKeyword = Token<SyntaxKind.AbstractKeyword>`); a
          // reference's otherwise.
          const actuals = type.getAliasSymbol() ? type.getAliasTypeArguments()
            : isTypeReference(type) ? checker.getTypeArguments(type) : [];
          const args = actuals.map(argument => contextualTerm(argument, span));
          // A type declared in a block closing over a type parameter has
          // arguments TypeScript's type does not state.
          if (args.length !== parametersOf(node).length)
            throw Error(`the contextual type ${text()} does not state every declaration argument`);
          if (computedMembers(node)) throw Error(`the contextual type ${text()} needs a written application to read its computed members`);
          const declared = declarationOf([node], text());
          contextualStarts.push({ node: declared, span });
          return { k: "reference", reference: { name: node.name.text, span, arguments: args.map(() => span), target: identityOf(node) },
            args, span };
        }
        if (type.isUnionType() || type.isIntersectionType()) {
          const parts = (type.getTypes() ?? []).map(part => contextualTerm(part, span));
          const [only] = parts;
          return parts.length === 1 && only ? only : { k: type.isUnionType() ? "union" : "intersection", parts, span };
        }
        if (type.isTypeParameter()) {
          const name = type.getSymbol()?.name;
          if (name) return { k: "binder", name, span };
        }
        if (checker.isArrayType(type) && isTypeReference(type)) {
          const [element] = checker.getTypeArguments(type);
          if (element) return { k: "array", presence: "readable", readonly: type.getSymbol()?.name === "ReadonlyArray",
            element: contextualTerm(element, span), span };
        }
        // A tuple of required positions and a rest, as its annotation reads,
        // readonly as TypeScript says. An optional position's type TypeScript
        // gives with `undefined` whether or not it was written, so it is not
        // read.
        const tuple = checker.isTupleType(type) && isTypeReference(type) ? type.getTarget() : undefined;
        if (tuple && isTupleType(tuple) && isTypeReference(type)) {
          const elements = checker.getTypeArguments(type);
          const required: TypeTerm[] = [];
          let rest: TypeTerm | null = null;
          for (const [i, flag] of tuple.elementFlags.entries()) {
            const element = elements[i];
            if (!element) throw Error(`the contextual tuple ${text()} states no type at position ${i}`);
            if (flag === ElementFlags.Required && rest === null) required.push(contextualTerm(element, span));
            else if (flag === ElementFlags.Rest && rest === null) rest = contextualTerm(element, span);
            else throw Error(`TypeScript types this unannotated closure parameter from its context as ${text()}, ` +
              "a tuple with an optional or variadic position, which an annotation states");
          }
          return { k: "tuple", presence: "dense", readonly: tuple.readonly, required, optional: [], rest, span };
        }
        const callable = contextualCallable(type, span);
        if (callable) return callable;
        const record = contextualRecord(type, span);
        if (record) return record;
        // A library regex type (`RegExpExecArray` for a match's callback), as
        // `regexp.mts` reads it.
        const library = nodes.filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
        if (symbol && library.length && library.length === nodes.length &&
            library.every(n => libraryFile(n.getSourceFile()))) {
          const stated = libraryRegExp(symbol.name, library);
          if (stated) return stated;
        }
        throw Error(`TypeScript types this unannotated closure parameter from its context as ${text()}, which is ` +
          "not stated by primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name");
      } finally {
        typesRead.delete(type.id);
      }
    };
    const parameterAt = (span: Span): ts.ParameterDeclaration | null => {
      const visit = (node: Node): ts.ParameterDeclaration | null => {
        if (ts.isParameterDeclaration(node) && node.name.getStart(client) === span[0] && node.name.end === span[1]) return node;
        return node.getStart(client) <= span[0] && span[1] <= node.end ? node.forEachChild(visit) ?? null : null;
      };
      return visit(client);
    };
    for (const span of options.staticTypes ?? []) {
      const name = identifierAt(client, span);
      if (!name) throw new DeclarationError(span, "TypeScript static field missing");
      const symbol = checker.getSymbolAtLocation(name);
      const type = symbol ? checker.getTypeOfSymbol(symbol) : undefined;
      try {
        if (!type || type.isErrorType()) throw Error("TypeScript gives this static field no type");
        options.staticType?.(span, { ok: true, value: contextualTerm(type, span) });
      } catch (error) {
        options.staticType?.(span, { ok: false, refused: refusalAt(span, error) });
      }
    }
    for (const span of options.contextualParams ?? []) {
      const parameter = parameterAt(span);
      if (!parameter) throw new DeclarationError(span, "TypeScript parameter missing");
      const type = checker.getTypeAtLocation(parameter.name);
      try {
        if (!type || type.isErrorType()) throw Error("TypeScript gives this unannotated closure parameter no type");
        options.contextualParam?.(span, { ok: true, value: contextualTerm(type, span) });
      } catch (error) {
        options.contextualParam?.(span, { ok: false, refused: refusalAt(span, error) });
      }
    }
    // `Object.assign(arrow, literal)` without type arguments: the two
    // TypeScript infers, `T` the arrow's type, one call signature of terms
    // `contextualTerm` states, and `U` the literal's record (`inferredTerm`).
    // Both are annotations the callable form checks the arrow and the
    // literal at.
    for (const span of options.assignCalls ?? []) {
      const call = expressionAt(client, span);
      if (!call || !ts.isCallExpression(call)) throw new DeclarationError(span, "TypeScript Object.assign call missing");
      try {
        const resolved = checker.getResolvedSignature(call);
        const target = resolved && checker.getParameterType(resolved, 0);
        const source = resolved && checker.getParameterType(resolved, 1);
        if (!target || !source) throw Error("TypeScript resolves no signature of this Object.assign call");
        const [signature, ...others] = checker.getSignaturesOfType(target, SignatureKind.Call);
        const arrow = call.arguments[0];
        if (!signature || others.length || signature.getTypeParameters().length || !arrow ||
            !ts.isArrowFunction(arrow) || arrow.parameters.some(p => p.dotDotDotToken || p.questionToken || p.initializer))
          throw Error(`TypeScript infers Object.assign's target as ${checker.typeToString(target)}, not one ` +
            "call signature of required parameters");
        const params = signature.getParameters().map(p => {
          const type = checker.getTypeOfSymbol(p);
          if (!type) throw Error("TypeScript gives an Object.assign target's parameter no type");
          return contextualTerm(type, span);
        });
        const returned = checker.getReturnTypeOfSignature(signature);
        if (!returned) throw Error("TypeScript gives an Object.assign target no result type");
        const bagType = inferredTerm(checker, source, span);
        if (!bagType || bagType.k !== "object")
          throw Error(`TypeScript infers Object.assign's source as ${checker.typeToString(source)}, not an object ` +
            "literal's record of literals and primitives");
        options.assignTypes?.(span, { ok: true, value: { bagType, functionType: { k: "function", effect: ordinaryEffect,
          receiver: null, params, rest: null, result: contextualTerm(returned, span), span } } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.assignTypes?.(span, { ok: false, refused: "the type arguments TypeScript infers for this Object.assign: " +
          refusalAt(span, error) });
      }
    }
    for (const span of options.enums ?? []) {
      const statement = client.statements.find(s => s.getStart(client) === span[0] && s.end === span[1]);
      if (!statement || !ts.isEnumDeclaration(statement))
        throw new DeclarationError(span, "TypeScript enum declaration missing");
      try {
        clean(statement, `enum ${statement.name.text}`);
      } catch (error) {
        recover(span, error);
        continue;
      }
      const members = statement.members.map(member => {
        const value = checker.getConstantValue(member);
        options.enumMember?.([member.getStart(client), member.end], value);
        return { node: member, name: ts.isIdentifier(member.name) || ts.isStringLiteral(member.name) ? member.name.text : "", value };
      });
      const modifier = (kind: ts.SyntaxKind) => !!statement.modifiers?.some(m => m.kind === kind);
      if (modifier(ts.SyntaxKind.ConstKeyword)) continue;
      const at: Span = [statement.getStart(client), statement.end];
      // An ambient enum is the environment's object, read as a `declare
      // const` of its members' object type is (`enumMembersTerm`).
      if (modifier(ts.SyntaxKind.DeclareKeyword)) {
        values.push({ binding: { local: statement.name.text, imported: statement.name.text, specifier: ambientSpecifier, span: at },
          declaration: { module: idOf(client), name: statement.name.text, span: at }, construct: false, typeParams: [],
          type: enumMembersTerm(members, at, "none") });
        continue;
      }
      if (members.every(m => m.value !== undefined)) continue;
      // An enum with a member whose value is known only at run time is built
      // by `%Enum:E%` (`enumIntrinsic`). A read in a member's initializer of
      // a member of the same enum, bare or `E.M`, `E["M"]`, is reported to
      // `enumMemberRead` with the member's span.
      const intrinsic = enumIntrinsic(statement.name.text, members);
      values.push({ binding: { local: intrinsic.name, imported: intrinsic.name, specifier: intrinsicModule, span: at },
        declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
        construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
      const same = (a: Node | undefined, b: Node): boolean => !!a && a.getSourceFile() === client && a.pos === b.pos && a.end === b.end;
      const ownMember = (node: Node | undefined): Node | undefined =>
        node && ts.isEnumMember(node) ? members.find(m => same(node, m.node))?.node : undefined;
      const ownEnum = (node: Node): boolean => ts.isIdentifier(node) &&
        !!targetOf(checker, node)?.declarations.some(d => same(d.resolve(), statement));
      const memberNamed = (name: string): Node | undefined => members.find(m => m.name === name)?.node;
      const report = (read: Node, member: Node): void => {
        options.enumMemberRead?.([read.getStart(client), read.end], [member.getStart(client), member.end]);
      };
      // `forEachChild` stops at a callback's truthy result: `visit` has none.
      const visit = (node: Node): void => {
        if (ts.isPropertyAccessExpression(node) && ownEnum(node.expression)) {
          const member = memberNamed(node.name.text);
          if (member) return report(node, member);
        }
        if (ts.isElementAccessExpression(node) && ownEnum(node.expression) &&
            ts.isStringLiteral(node.argumentExpression)) {
          const member = memberNamed(node.argumentExpression.text);
          if (member) return report(node, member);
        }
        if (ts.isPropertyAccessExpression(node)) return visit(node.expression);
        if (ts.isIdentifier(node)) {
          const member = ownMember(targetOf(checker, node)?.declarations[0]?.resolve());
          if (member) report(node, member);
          return;
        }
        node.forEachChild(visit);
      };
      for (const m of members) if (m.value === undefined && m.node.initializer) visit(m.node.initializer);
    }
    for (const span of options.constEnumReads ?? []) {
      const access = expressionAt(client, span);
      if (!access || !(ts.isPropertyAccessExpression(access) || ts.isElementAccessExpression(access)) ||
          !ts.isIdentifier(access.expression))
        throw new DeclarationError(span, "TypeScript enum member read missing");
      const owners = targetOf(checker, access.expression)?.declarations.map(d => d.resolve()) ?? [];
      const [owner] = owners;
      const value = checker.getConstantValue(access);
      if (owners.length === 1 && owner && ts.isEnumDeclaration(owner) && owner.parent === client &&
          owner.modifiers?.some(m => m.kind === ts.SyntaxKind.ConstKeyword) && value !== undefined)
        options.constEnumRead?.(span, value);
    }
    for (const span of options.keyTypes ?? []) {
      const node = typeNodeAt(client, span);
      try {
        options.keyType?.(span, node ? keyTypeOf(node) : null);
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    for (const span of options.mappedTypes ?? []) {
      const node = typeNodeAt(client, span);
      try {
        options.mappedType?.(span, node && ts.isMappedTypeNode(node) ? mappedModifiersOf(node) : null);
      } catch (error) {
        recover(span, error);
        continue;
      }
    }
    for (const span of options.symbolNames ?? []) {
      const node = expressionAt(client, span);
      if (!node || !(ts.isIdentifier(node) || ts.isPropertyAccessExpression(node))) {
        options.symbolName?.(span, { ok: false, refused: "a computed key names a symbol constant" });
        continue;
      }
      try {
        const literal = literalKeyOf(node);
        const type = checker.getTypeAtLocation(node);
        const value = type?.isStringLiteralType() || type?.isNumberLiteralType() ? type.value : null;
        options.symbolName?.(span, { ok: true, value: literal !== null && value !== null ? { literal, value } : symbolOf(node) });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.symbolName?.(span, { ok: false, refused: refusalAt(span, error) });
      }
    }
    // The client's computed types: each evaluated where it is written, with
    // the binders of the functions around it, or refused with the reason.
    for (const span of options.computed ?? []) {
      const node = computedAt(client, span);
      if (!node) throw new DeclarationError(span, "TypeScript computed type missing");
      // A global or an imported type's application is computed when the alias it names is.
      const alias = ts.isTypeReferenceNode(node) ? aliasOf(node) : null;
      const aggregate = ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)
        && typeDeclarationsOf(node.typeName).some(d => ts.isClassDeclaration(d) || ts.isInterfaceDeclaration(d))
        ? lookup(node.typeName, node.typeName.text) : null;
      if (ts.isTypeReferenceNode(node) && !(alias && computedAlias(alias, aliasOf)) && !(aggregate && computedMembers(aggregate))) continue;
      const what = `${idOf(client)}#${node.getText(client)}`;
      const scope = valueScope(node, what, enclosingBinders(node));
      try {
        options.computedType?.(span, { ok: true, value: aggregate && computedMembers(aggregate) ? typeTerm(scope, node)
          : computedType(computedContext, node, span, part => typeTerm(scope, part)) });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.computedType?.(span, { ok: false, refused: refusalAt(span, error) });
      }
    }
    // The client's references to types declared in its blocks, each the
    // declaration TypeScript binds it to; one TypeScript computes from its
    // parameters is a computed type above.
    const blockStarts: { node: TypeDeclaration; span: Span }[] = [];
    for (const span of options.blockTypes ?? []) {
      const node = typeNodeAt(client, span);
      if (!node || !ts.isTypeReferenceNode(node) || !ts.isIdentifier(node.typeName))
        throw new DeclarationError(span, "TypeScript type reference missing");
      const name = node.typeName;
      const declared = typeDeclarationsOf(name);
      if (!declared.some(d => (ts.isTypeAliasDeclaration(d) || ts.isInterfaceDeclaration(d)) &&
          !!d.parent && !ts.isSourceFile(d.parent) && !ts.isModuleBlock(d.parent)))
        continue;
      try {
        const target = lookup(name, name.text);
        const what = `${idOf(client)}#${name.text}`;
        if (ts.isTypeAliasDeclaration(target) && associatedAlias(target))
          throw Error(`an associated-result alias declared in a block is outside the fragment: ${what}`);
        const computed = computedAlias(target, aliasOf);
        const captured = capturedOf(target);
        for (const parameter of captured) capturedAt(node, what)(parameter);
        const own = parametersOf(target).filter(p => !p.captured);
        if (!computed) blockStarts.push({ node: target, span });
        options.blockType?.(span, { ok: true, value: { computed, declaration: identityOf(target),
          captured: captured.map(p => p.name.text), required: own.filter(p => !p.default).length, total: own.length } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.blockType?.(span, { ok: false, refused: refusalAt(span, error) });
      }
    }
    // The client's references that omit arguments of a declaration: the
    // omitted ones completed at the written ones (`completeArguments`) and
    // reported to `completion`, or refused with the reason.
    const completing = (node: Node): void => {
      if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)) {
        const name = node.typeName;
        const written = node.typeArguments ?? [];
        const targets = typeDeclarationsOf(name).filter(isTypeDeclaration);
        // A library type read at its meaning completes its own arguments.
        if (targets.some(t => (t.typeParameters?.length ?? 0) > written.length) && !library(name, name.text)) {
          const span: Span = [node.getStart(client), node.end];
          try {
            const target = lookup(name, name.text);
            if (!computedAlias(target, aliasOf)) {
              const scope = valueScope(node, `${idOf(client)}#${node.getText(client)}`, enclosingBinders(node));
              const closed = capturedOf(target).length;
              const completed = completeArguments(target, written.map(arg => typeTerm(scope, arg)), node, name.text,
                capturedAt(node, name.text));
              options.completion?.(span, { ok: true, value: completed.slice(closed + written.length) });
            }
          } catch (error) {
            if (error instanceof DeclarationError) throw error;
            options.completion?.(span, { ok: false, refused: refusalAt(span, error) });
          }
        }
      }
      node.forEachChild(completing);
    };
    if (options.completion) completing(client);
    // The applications written in the client file and in the declarations it
    // reaches (`written-applications.mts`), each target joining the graph for
    // its bounds; a library one is stated for its bounds only.
    const sweepScope = (at: Node, binder: (declaration: ts.TypeParameterDeclaration) => string | undefined): TermScope => {
      const what = `${idOf(at.getSourceFile())}#${at.getText(at.getSourceFile())}`;
      const base = valueScope(at, what, [], parameter => {
        const name = binder(parameter);
        if (name === undefined)
          throw Error(`a type declared in a block closes over ${parameter.name.text}, which the written application's scope in ${what} does not bind`);
        return { k: "binder", name, span: [at.getStart(at.getSourceFile()), at.end] };
      });
      return { ...base, named: (part, pos, read) => {
        // A merged declaration's parameter is one per part: the one in scope.
        const parameters = (ts.isIdentifier(part.typeName) ? typeDeclarationsOf(part.typeName) : [])
          .filter(ts.isTypeParameterDeclaration);
        const [first] = parameters;
        if (first) {
          const name = parameters.map(binder).find(n => n !== undefined);
          if (!name || part.typeArguments?.length)
            throw Error(`the type parameter ${first.name.text} in ${what} is not one the written application's scope binds`);
          return { k: "binder", name, span: pos };
        }
        return base.named(part, pos, read);
      } };
    };
    // What a symbol denotes for the sweep (`Entity`): its declarations, an
    // alias followed to its target, and the symbols its type exposes as
    // members, as the checker has them: a class's instance and static
    // members, a module's or namespace's exports, `export =` and a default
    // export included.
    type Symbolic = NonNullable<ReturnType<typeof targetOf>>;
    const follow = (symbol: Symbolic | undefined): Symbolic | undefined =>
      symbol && symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
    const exportsOf = (symbol: Symbolic): Symbolic[] => {
      const found = new Map<number, Symbolic>();
      if (symbol.flags & (SymbolFlags.ValueModule | SymbolFlags.NamespaceModule)) {
        for (const e of checker.getExportsOfModule(symbol)) found.set(e.id, e);
        for (const [key, e] of symbol.getExports()) if (key === "export=" || key === "default") found.set(e.id, e);
      }
      if (symbol.flags & SymbolFlags.Class) {
        for (const e of symbol.getMembers().values()) found.set(e.id, e);
        for (const [key, e] of symbol.getExports()) if (key !== "prototype") found.set(e.id, e);
      }
      return [...found.values()];
    };
    // A symbol the checker synthesises has no declaration: no entity. Its
    // origin is found where it is selected (`resolve`, `members`).
    const entityOf = (symbol: Symbolic | undefined): Entity | null => {
      const target = follow(symbol);
      if (!target || checker.isUnknownSymbol(target)) return null;
      const declarations = target.declarations.map(d => d.resolve()).filter((d): d is Node => !!d);
      if (!declarations.length) return null;
      return { declarations,
        members: () => exportsOf(target).map(e => entityOf(e) ?? { declarations: [], members: () => [] }) };
    };
    let applications: WrittenApplication[] = [];
    try {
      applications = writtenApplications({
        ...(options.diagnostic ? { diagnostic: (pos: Span | null, reason: string): void =>
          recover(pos ?? options.root ?? [0, 0], Error(reason)) } : {}),
        declarationsOf: typeDeclarationsOf,
        declaration: name => {
          const nodes = typeDeclarationsOf(name);
          if (!nodes.some(isTypeDeclaration)) return null;
          // A statement, `Within<F, T>`, is no application: the reader of
          // signatures reads its footprint, whose shape it checks
          // (`statedResult`), and its result.
          if (verifierAlias(name) === "Within") return null;
          // A target matters only where it has a bounded parameter.
          if (!nodes.some(n => isTypeDeclaration(n) && n.typeParameters?.some(p => p.constraint))) return null;
          const node = lookup(name, name.text);
          return partners.get(node) ?? [node];
        },
        library: node => libraryFile(node.getSourceFile()),
        // A host class's members are its view's (reading rule 4).
        admits: member => member.declarations.length === 0 || member.declarations.some(d => {
          const owner = d.parent;
          if (!owner || !ts.isClassDeclaration(owner) || !compilerApiFile(d.getSourceFile().fileName)) return true;
          const view = hostViews.find(v => v.owner === owner.name?.text)?.members ?? [];
          return view.some(entry => d.getText(d.getSourceFile()).trim() === entry.text);
        }),
        read: (node, binder) => typeTerm(sweepScope(node, binder), node),
        reference: (name, args) => {
          const node = lookup(name, name.text);
          const source = name.getSourceFile();
          return { name: name.text, span: [name.getStart(source), name.end],
            arguments: args.map((arg): Span => [arg.getStart(source), arg.end]), target: identityOf(node) };
        },
        instantiate: instantiateAt,
        parameters: parametersOf,
        complete: completeArguments,
        resolve: name => {
          // The declarations a name denotes: TypeScript's symbol at its
          // location, or, for a step of a member path TypeScript gives no
          // symbol, a module's or namespace's export of that name; none for
          // a member the checker synthesises.
          const resolved = (at: Identifier): { symbol: Symbolic | null; entity: Entity } | null => {
            const direct = follow(checker.getSymbolAtLocation(at));
            const entity = entityOf(direct);
            if (direct && entity) return { symbol: direct, entity };
            // The values the language defines, which no declaration states.
            if (direct && !direct.declarations.length && (direct.name === "undefined" || direct.name === "globalThis"))
              return { symbol: direct, entity: { declarations: [], members: () => [], intrinsic: true } };
            const path = at.parent;
            if (!path || !ts.isQualifiedName(path) || path.right !== at) return null;
            const left = ts.isIdentifier(path.left) ? path.left : path.left.right;
            const owner = ts.isIdentifier(left) ? resolved(left) : null;
            if (!owner) return null;
            const exported = owner.symbol ? follow(exportsOf(owner.symbol).find(e => e.name === at.text)) : undefined;
            const selected = entityOf(exported);
            if (exported && selected) return { symbol: exported, entity: selected };
            return null;
          };
          return resolved(name)?.entity ?? null;
        },
        moduleOf: specifier => entityOf(checker.getSymbolAtLocation(specifier)),
        members: (object, key) => {
          const type = checker.getTypeFromTypeNode(object);
          if (!type) return [];
          const keyType = key ? checker.getTypeFromTypeNode(key) : null;
          const parts = keyType ? (keyType.isUnionType() ? keyType.getTypes() : [keyType]) : [];
          const literals = parts.length && parts.every(p => p.isStringLiteralType() || p.isNumberLiteralType())
            ? parts.map(p => p.isStringLiteralType() ? p.value : p.isNumberLiteralType() ? String(p.value) : "") : null;
          const properties = literals ? literals.map(k => checker.getPropertyOfType(type, k)) : checker.getPropertiesOfType(type);
          // A member the checker synthesises without a declaration is
          // refused by the sweep (an entity without declarations).
          return properties.map(p => entityOf(p) ?? { declarations: [], members: () => [] });
        },
        module: file => idOf(file),
        client,
      }, [client, ...valueDeclarations]);
    } catch (error) {
      recover(error instanceof SweepError ? error.span ?? [0, 0] : [0, 0], error);
    }
    const seen = new Set<string>();
    const definitions: TypeDefinition[] = [];
    const records = new Set<string>();
    const starts = [
      ...roots.map(({ root, node }) => ({ node, span: root.binding.span })),
      ...valueStarts.map((node, index): { node: TypeDeclaration; span: Span } =>
        ({ node, span: values[Math.min(index, values.length - 1)]?.binding.span ?? [0, 0] })),
      ...contextualStarts,
      ...blockStarts,
    ];
    const collectFrom = (list: readonly { node: TypeDeclaration; span: Span; instance?: DeclarationInstance }[]): void => {
      for (const { node: start, span, instance } of list) {
        try {
          collect(start, seen, definitions, { diagnostic: options.diagnostic ? (identity, reason) =>
              recover(span, Error(`${identity.module}#${identity.name}: ${reason}`)) : undefined, complete: completeArguments, parameters: parametersOf, lookup,
            computedMembers, instanceOf, instantiate: instantiateAt,
            enumType: enumTypeAt, enumerated, memberName, identityOf, isBrand, libraryFile, hostType, symbol: symbolOf, literalKey: literalKeyOf, privateName: privateNameOf, partners, library, equation,
            libraryInterface, collectionIterator, computed: (node, span, read) => computedType(computedContext, node, span, read), family: familyOf,
            guardPromises,
            keys: keyTypeOf, modifiers: mappedModifiersOf, alias: aliasOf, awaited, stated: statement,
            record: identity => {
              records.add(definitionKey(identity));
              options.record?.(identity);
            },
            collecting: (node, key) => {
              collecting = key;
              if (node && key !== null && ts.isClassDeclaration(node) && programFile(node.getSourceFile()) && !ambient(node))
                programClasses.add(key);
            } }, instance);
        } catch (error) {
          throw new DeclarationError(span, messageOf(error), error);
        } finally {
          collecting = null;
        }
      }
    };
    const queuedValues = valueStarts.length;
    collectFrom(starts);
    let collectedInstances = 0;
    const collectInstances = (): void => {
      while (collectedInstances < instances.size) {
        const pending = [...instances.values()].slice(collectedInstances);
        collectedInstances = instances.size;
        collectFrom(pending.map(instance => ({ node: instance.node,
          span: [instance.use.getStart(instance.use.getSourceFile()), instance.use.end], instance })));
      }
    };
    collectInstances();
    // A value a definition names through `typeof` is read while the graph
    // is collected; the declarations its type names join the graph.
    for (let from = queuedValues; from < valueStarts.length;) {
      const to = valueStarts.length;
      const at = starts[0]?.span ?? [0, 0];
      collectFrom(valueStarts.slice(from, to).map(node => ({ node, span: at })));
      collectInstances();
      from = to;
    }
    // An array type reaching the unit only through a declaration (an
    // imported value's, a declared type's member, a library contract's) is
    // read at `Array.prototype`'s contract as one the client writes is; the
    // declarations that contract names join the graph.
    if (!arrayProto.length &&
        [values, definitions, applications, selections, primitiveProtos, regexpDefinitions, collectionDefinitions].some(namesArray)) {
      const at = values[0]?.binding.span ?? roots[0]?.root.binding.span ?? [0, 0];
      const from = valueStarts.length;
      try {
        arrayProto = arrayPrototype(checker, client, overlayLibrary, options.arrayOverlay ?? overlay);
      } catch (error) {
        throw new DeclarationError(at, messageOf(error), error);
      }
      collectFrom(valueStarts.slice(from).map(node => ({ node, span: at })));
    }
    definitions.push(...selections, ...primitiveProtos, ...regexpDefinitions, ...collectionDefinitions, ...(stableListed ? [stableDefinition] : []));
    // First, so its row follows the four fixed ones in every table.
    definitions.unshift(...arrayProto);
    // The graph is complete: each mapped type read at a named type before
    // its definition was is expanded at it (`settleDocument`).
    const settledAt = starts[0]?.span ?? [0, 0];
    const settledDocument = settleDocument({ definitions, values, applications }, id => records.has(definitionKey(id)),
      (_where, error) => {
        recover(settledAt, error);
        return { k: "atom", name: "unknown", span: settledAt };
      });
    definitions.splice(0, definitions.length, ...settledDocument.definitions);
    values.splice(0, values.length, ...settledDocument.values);
    applications = settledDocument.applications;
    // Trusted generic promise results have a stable non-thenable payload
    // contract, so fresh resolution preserves that payload. Bound each
    // type parameter a Promise or PromiseLike position names accordingly
    // (SOURCE-CONTRACTS.md, "Async functions and await"). An existing
    // fulfilled promise may retain an object that later acquires then.
    // The client's own bodies are checked at their source annotations.
    externalStatements(externalTypes, definitions, statedDefinitions, programClasses);
    const clientModule = idOf(client);
    const trustedValues = values.map(v => v.binding.specifier === intrinsicModule ? v :
      { ...v, typeParams: promisedBinders(v.typeParams, v.type), type: promisedMethods(v.type) });
    const localInstances = new Set([...instances.values()].filter(i => idOf(i.node.getSourceFile()) === clientModule).map(i => i.identity.module));
    const trustedDefinitions = definitions.map(d => d.declaration.module === clientModule || localInstances.has(d.declaration.module) ? d :
      { ...d, expression: d.expression && promisedMethods(d.expression) });
    if (options.familySelected) options.familySelected(scan());
    const document: DeclarationDocument = { roots: roots.map(r => r.root), definitions: trustedDefinitions, values: trustedValues, symbols, applications };
    if (deferredIn(document))
      throw new DeclarationError(settledAt, "a mapped type over a named type is left unexpanded in the declaration document");
    return document;
  });
}

/** A value declared outside the program's sources (a package, a declaration
 * file, an ambient declaration) is the environment's: a statement its type
 * reaches, through a reference to a definition whose equation reads one,
 * would state an effect of code no run checks. A program class's members are
 * the exception: its instances are the program's values, whose conformance
 * external code preserves (DESIGN.md, "Trust surface"). */
function externalStatements(externals: readonly { what: string; type: TypeTerm }[],
    definitions: readonly TypeDefinition[], stated: ReadonlySet<string>, classes: ReadonlySet<string>): void {
  const keyOf = (id: DeclarationIdentity) => `${id.module}#${id.span[0]}:${id.span[1]}`;
  const byKey = new Map(definitions.map(d => [keyOf(d.declaration), d] as const));
  for (const { what, type } of externals) {
    const seen = new Set<string>();
    const work: TypeTerm[] = [type];
    for (let term = work.pop(); term !== undefined; term = work.pop())
      visitType(term, part => {
        if (part.k !== "reference") return;
        const key = keyOf(part.reference.target);
        if (seen.has(key) || classes.has(key)) return;
        seen.add(key);
        if (stated.has(key))
          throw Error(`the value ${what}, declared outside the program's sources, is typed through ${part.reference.name}, whose statement (\`Within\`) states an effect of code no run checks`);
        const definition = byKey.get(key);
        if (definition?.expression) work.push(definition.expression);
        work.push(...definition?.bases ?? []);
      });
  }
}

/** TypeScript's "implicitly has an 'any' type" (TS7008) on a field an
 * ambient class declares without a type: nothing defines the class here, so
 * the field is only read, at `unknown` (`classInstance`), never at the `any`
 * TypeScript gives it. */
function untypedAmbientField(file: SourceFile, d: { code: number; pos: number; end: number }): boolean {
  if (d.code !== 7008) return false;
  const inside = (node: Node) => node.getStart(file) <= d.pos && d.end <= node.end;
  return file.statements.some(s => ts.isClassDeclaration(s) && inside(s) &&
    s.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword) === true &&
    s.members.some(m => ts.isPropertyDeclaration(m) && !m.type && inside(m.name)));
}

/** The binders a `Promise<…>` or `PromiseLike<…>` argument of `type` names. */
function promisedNames(type: TypeTerm): Set<string> {
  const names = new Set<string>();
  const visit = (t: TypeTerm, inside: boolean): void => {
    switch (t.k) {
      case "binder": if (inside) names.add(t.name); return;
      case "reference": {
        const promise = (t.reference.name === "Promise" || t.reference.name === "PromiseLike") &&
          /typescript\/lib\//.test(t.reference.target.module);
        for (const a of t.args) visit(a, inside || promise);
        return;
      }
      case "union": case "intersection": for (const p of t.parts) visit(p, inside); return;
      case "array": visit(t.element, inside); return;
      case "tuple": for (const p of [...t.required, ...t.optional, ...(t.rest ? [t.rest] : [])]) visit(p, inside); return;
      case "object":
        for (const f of t.fields) visit(f.type, inside);
        for (const c of t.calls) visit(c, inside);
        if (t.stringIndex) visit(t.stringIndex.value, inside);
        if (t.numberIndex) visit(t.numberIndex.value, inside);
        if (t.symbolIndex) visit(t.symbolIndex.value, inside);
        if (t.prototype) visit(t.prototype, inside);
        return;
      case "function": case "constructor":
        for (const p of t.params) visit(p, inside);
        if (t.rest) visit(t.rest, inside);
        visit(t.result, inside);
        if (t.k === "function" && t.receiver) visit(t.receiver, inside);
        if (t.k === "constructor") t.statics?.forEach(field => visit(field.type, inside));
        return;
      case "scheme":
        for (const b of t.binders) {
          if (b.bound) visit(b.bound, inside);
          if (b.default) visit(b.default, inside);
        }
        for (const f of t.signatures) visit(f, inside); return;
      case "pack": visit(t.of, inside); return;
      default: return;
    }
  };
  visit(type, false);
  return names;
}
/** Each binder a promise argument names, bounded by `nonThenable` as well. */
function promisedBinders<B extends { name: string; bound: TypeTerm | null }>(binders: B[], type: TypeTerm): B[] {
  const promised = promisedNames(type);
  return binders.map(b => !promised.has(b.name) ? b : { ...b, bound: b.bound === null ? nonThenable
    : { k: "intersection", span: b.bound.span, parts: [b.bound, nonThenable] } });
}
/** The generic methods of a type, each binder a promise argument names
 * bounded by `nonThenable`. */
function promisedMethods(type: TypeTerm): TypeTerm {
  const mapped = mapTypeParts(type, promisedMethods);
  return mapped.k === "scheme" ? { ...mapped, binders: promisedBinders(mapped.binders, mapped) } : mapped;
}

/** The specifier of a primitive wrapper's prototype: the built-ins', which no
 * import names. */
const prototypeSpecifier = "prototype";
/** The specifier of a global value's binding: no import names it. */
const globalSpecifier = "global";
/** The specifier of an ambient declaration's binding, `declare function f`:
 * the client states the value's type and nothing defines it. */
const ambientSpecifier = "ambient";

type SelectionContext = {
  lookup: (identifier: Identifier, what: string) => TypeDeclaration;
  identityOf: (file: SourceFile) => string;
  /** Whether a file is the standard library's (`moduleIds`). */
  libraryFile: (file: SourceFile) => boolean;
  clean: (node: Node, what: string) => void;
  valueScope: (node: Node, what: string) => TermScope;
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>;
  /** The reviewed overlay a standard library global is read through. */
  overlay: readonly GlobalEntry[];
  /** Told each call the overlay reads as a test of the calculus. */
  test: (span: Span, test: NonNullable<GlobalEntry["test"]>) => void;
  /** Told each call the overlay reads as a call of an intrinsic. */
  intrinsic: (span: Span, name: string) => void;
  /** Told each call the overlay reads as the global's construct. */
  construct: (span: Span) => void;
  /** Given each declaration a read entry's statement names that no library
   * declares (`GlobalEntry.definitions`). */
  define: (definition: TypeDefinition) => void;
  /** A standard library interface applied to `args`, for a statement that
   * names one (`new Set<T>()` gives a `Set<T>`). */
  library: (name: string, args: TypeTerm[]) => TypeTerm;
};

/** Whether a reference is written: an assignment's target or an update's
 * operand. */
function isWritten(use: Identifier): boolean {
  const parent = use.parent;
  if (ts.isBinaryExpression(parent) && parent.left === use)
    return parent.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      parent.operatorToken.kind <= ts.SyntaxKind.LastAssignment;
  return (ts.isPrefixUnaryExpression(parent) || ts.isPostfixUnaryExpression(parent)) &&
    (parent.operator === ts.SyntaxKind.PlusPlusToken || parent.operator === ts.SyntaxKind.MinusMinusToken);
}

/** A call at a stated signature passes no argument past its parameters but
 * to its rest, the only one a spread may reach. */
function boundedArguments(call: ts.CallExpression, stated: Stated, what: string): void {
  if (stated.rest) {
    if (call.arguments.slice(0, stated.params.length).some(ts.isSpreadElement))
      throw Error(`${what} is read with spreads past its ${stated.params.length} parameter(s) only`);
    return;
  }
  if (call.arguments.length > stated.params.length || call.arguments.some(ts.isSpreadElement))
    throw Error(`${what} is read with at most ${stated.params.length} argument(s)`);
}

/**
 * A global variable, such as Node's `process` or the standard library's
 * `BigInt`, read at the members and call signatures the client's references
 * `uses` select (SOURCE-CONTRACTS.md, "Imported, ambient and global values"
 * and "Library globals"). Every
 * reference must read a member by name, `process.m`, or be called,
 * `BigInt(v)`. TypeScript resolves the member on the interface the variable
 * is annotated with, through its heritage and merged declarations, and a
 * call to one of that interface's call signatures. An interface of the same
 * name, `interface BigInt` beside `declare var BigInt`, is the name's type
 * meaning, which a value reference does not denote. The definition, keyed by
 * the variable's first declaration, is an object with one member per name
 * read, and the call signatures the client's calls resolve to:
 *
 * - a method is the overloads TypeScript resolves the client's calls to,
 *   each a host-relative member (so its reference must be called), and a
 *   `this` result is the definition itself, the host;
 * - a property is its signature as declared, read like any declaration's;
 * - a call signature is read as a method's is, with no receiver;
 * - a reference read as a value, `xs.filter(Boolean)`, selects every call
 *   signature, since whoever receives the value may call it at any; a
 *   standard library global only where the overlay states each for a value.
 *
 * Leaving the other members and signatures out gives a supertype of the
 * declared type, since methods are host-relative; nothing else about the
 * members read changes. A member inherited from a generic interface, and a
 * generic, optional or `this`-typed method or call signature, are refused.
 * A global the standard library declares is read only through the reviewed
 * overlay (`library-globals.mts`): each signature read must be listed, and a
 * parameter at which the host would run the client's code is stated at what
 * it accepts without running any.
 *
 * A global the client only constructs, `new Array<T>()`, is instead its
 * construct signatures, as a class value is: each the overlay's statement of
 * it, or, outside the standard library, as declared. A global read only
 * through tests, `Array.isArray(e)`, is no value at all (null).
 */
/** A declaration's type parameters by position, as TypeScript merges its
 * declarations `parts`: each position's parameter in the declaration
 * binding the longest list, and its bound and default with the declaration
 * stating them, in whose scope they are read. TypeScript requires the
 * declarations stating a position's bound, or its default, to agree. */
/** A declaration stating a position's type parameter, and the parameter there. */
type StatedParameter = { part: TypeDeclaration; at: ts.TypeParameterDeclaration };
/** A type parameter position of merged declarations: the longest list's
 * parameter there, and the first declaration stating its bound, its default. */
type MergedPosition = { parameter: ts.TypeParameterDeclaration; bound: StatedParameter | undefined;
  default: StatedParameter | undefined };
function mergedParameters(parts: readonly TypeDeclaration[]): MergedPosition[] {
  const longest = parts.reduce<readonly ts.TypeParameterDeclaration[]>((list, part) =>
    (part.typeParameters?.length ?? 0) > list.length ? part.typeParameters ?? [] : list, []);
  return longest.map((parameter, index) => {
    const stated = parts.flatMap(part => {
      const at = part.typeParameters?.[index];
      return at ? [{ part, at }] : [];
    });
    return { parameter, bound: stated.find(s => s.at.constraint), default: stated.find(s => s.at.defaultType) };
  });
}

/** A namespace declaring only types, directly or in namespaces of its own:
 * TypeScript makes no value of it, so in a value position the name means
 * only its other declarations (`console`, a variable and a namespace of
 * interfaces). */
function typesOnly(node: Node): boolean {
  if (!ts.isModuleDeclaration(node) || !node.body) return false;
  const body = node.body;
  return ts.isModuleBlock(body)
    ? body.statements.every(s => ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) || typesOnly(s))
    : typesOnly(body);
}

/** A global function, its overloads declared without bodies: its value's
 * call signatures, each overload a call resolves to. Its implementation is
 * outside what is verified, wherever the declaration lies (the standard
 * library, an installed package, a declaration file of the project): each
 * overload a call resolves to is read through the reviewed overlay, an
 * entry listing it with exactly the text reviewed, an augmentation's
 * included; any other is refused. The function is only called. */
function globalFunction(checker: Checker, name: string, uses: readonly Identifier[],
    overloads: readonly ts.FunctionDeclaration[], context: SelectionContext): { definition: TypeDefinition } {
  const spanOf = (node: Node): Span => [node.getStart(node.getSourceFile()), node.end];
  const where = (node: Node) => `${context.identityOf(node.getSourceFile())}#${name}`;
  const what = `${name}(…)`;
  const chosen = new Map<ts.FunctionDeclaration, ts.CallExpression[]>();
  for (const use of uses) {
    const call = use.parent;
    if (!ts.isCallExpression(call) || call.expression !== use || call.questionDotToken)
      throw Error(`the global function ${name} is only called`);
    const resolved = checker.getResolvedSignature(call)?.declaration?.resolve();
    const overload = overloads.find(o => resolved && o.pos === resolved.pos && o.end === resolved.end &&
      o.getSourceFile().fileName === resolved.getSourceFile().fileName);
    if (!overload) throw Error(`TypeScript resolves the call of ${name} to no overload it declares`);
    chosen.set(overload, [...chosen.get(overload) ?? [], call]);
  }
  const calls = [...chosen].flatMap(([overload, calls]): FunctionTerm[] => {
    const at = spanOf(overload);
    // The declaration matched to an entry by its exact text.
    const declared = overload.getText(overload.getSourceFile());
    const text = reviewedText(declared);
    const entry = globalEntry(context.overlay, name, undefined, signature => signature === declared,
      declarationOrigin(overload.getSourceFile(), context.libraryFile));
    if (!entry) throw Error(`${what} is not in the reviewed overlay of library globals: ${text}`);
    for (const definition of entry.definitions ?? []) context.define(definition);
    if (overload.typeParameters?.length && !entry.stated) throw Error(`${what} is generic`);
    if (entry && (entry.test || entry.intrinsic || entry.construct || entry.value || entry.admit))
      throw Error(`${what} is reviewed in a form a global function does not take`);
    const written = entry?.stated;
    const stated = typeof written === "function" ? written(context.library) : written;
    if (Array.isArray(stated)) throw Error(`${what} states several forms`);
    if (stated) {
      if (stated.binders.length) throw Error(`${what} is stated with binders`);
      for (const call of calls) boundedArguments(call, stated, what);
      return [{ k: "function", effect: entry?.effect ?? ordinaryEffect, receiver: null, params: stated.params,
        rest: stated.rest ?? null, result: stated.result, span: at }];
    }
    context.clean(overload, where(overload));
    return signatures(context.valueScope(overload, what), overload.parameters, overload.type, overload, at)
      .map(form => {
        if (form.receiver) throw Error(`${what} states its receiver`);
        return { ...form, effect: entry?.effect ?? form.effect };
      });
  });
  const [declaration] = overloads;
  if (!declaration) throw Error(`the global function ${name} has no declaration`);
  const source = declaration.getSourceFile();
  return { definition: { declaration: { module: context.identityOf(source), name,
    span: [declaration.getStart(source), declaration.end] }, parameters: [], bases: [],
    expression: { k: "object", fields: [], stringIndex: null, calls, span: spanOf(uses[0] ?? declaration) } } };
}

/** Where a declaration comes from: the standard library (`library`), the
 * installed package of that name, its directory under `node_modules`
 * holding a `package.json` that names it (`@types/node`), or the project
 * (`project`). A reviewed entry admits one origin, so an identically spelled
 * declaration from another is no declaration it reviews. */
const origins = new Map<string, Remembered<string>>();
function declarationOrigin(file: SourceFile, libraryFile: (file: SourceFile) => boolean): string {
  if (libraryFile(file)) return "library";
  const path = realPath(file.fileName);
  return remembered(origins, path, () => originOf(path));
}
function originOf(path: string): string {
  const parts = path.split(sep);
  const at = parts.lastIndexOf("node_modules");
  const scope = parts[at + 1] ?? "";
  const name = scope.startsWith("@") ? `${scope}/${parts[at + 2] ?? ""}` : scope;
  let origin = "project";
  if (at >= 0 && name) {
    const directory = parts.slice(0, at + 1 + name.split("/").length).join(sep);
    // A directory without a manifest is the project's; a manifest that
    // cannot be read or parsed is no absence.
    const text = orAbsent(readText, join(directory, "package.json"));
    const manifest: unknown = text === null ? null : JSON.parse(text);
    if (manifest && typeof manifest === "object" && "name" in manifest && manifest.name === name) origin = name;
  }
  return origin;
}

function selectGlobal(checker: Checker, uses: readonly Identifier[], context: SelectionContext):
    { definition: TypeDefinition; construct?: never } |
    { construct: { declaration: DeclarationIdentity; typeParams: ValueRoot["typeParams"]; type: TypeTerm } } |
    null {
  const [first] = uses;
  if (!first) throw Error("a global value without a reference");
  const name = first.text;
  const declarations = (checker.getSymbolAtLocation(first)?.declarations ?? []).map(d => d.resolve());
  // A global declared as a function, `declare function parseInt(…)`, or a
  // function merged with a namespace (`setTimeout` and its `__promisify__`),
  // which is only called: the namespace's members are not read.
  const functions = declarations.filter((d): d is ts.FunctionDeclaration => !!d && ts.isFunctionDeclaration(d) && !d.body);
  if (functions.length && declarations.every(d => !!d && (ts.isFunctionDeclaration(d) || ts.isModuleDeclaration(d))))
    return globalFunction(checker, name, uses, functions, context);
  const variables = declarations.filter((d): d is ts.VariableDeclaration =>
    !!d && ts.isVariableDeclaration(d) && !!d.type && ts.isIdentifier(d.name));
  const [declaration] = variables;
  if (!declaration || declarations.some(d => !d ||
      (!ts.isInterfaceDeclaration(d) && !typesOnly(d) && !variables.some(v => v === d))))
    throw Error(`the global ${name} is not an annotated variable`);
  const where = (node: Node, key: string) => `${context.identityOf(node.getSourceFile())}#${key}`;
  for (const variable of variables) context.clean(variable, where(variable, name));
  // Every declaration of the variable comes from an origin its entries
  // admit: one from elsewhere states a value no entry reviews.
  const admitted = globalOrigins(context.overlay, name);
  for (const variable of variables) {
    const origin = declarationOrigin(variable.getSourceFile(), context.libraryFile);
    if (!admitted.has(origin))
      throw Error(`the global ${name} is declared in ${context.identityOf(variable.getSourceFile())} (${origin}), an origin no reviewed entry admits`);
  }
  const spanOf = (node: Node): Span => [node.getStart(node.getSourceFile()), node.end];
  // Every global is read through the reviewed overlay, wherever it is
  // declared (the standard library, an installed package such as Node's
  // `process`, a declaration file of the project): a member or signature it
  // does not list, with exactly the text reviewed, is refused.
  // An entry stating several forms states construct signatures: each form is
  // one, under the entry's binders, which every form names alike. Read
  // anywhere else, or empty, the list is refused rather than an arm dropped.
  const reviewedForms = (member: string | undefined, node: Node, what: string):
      (Omit<GlobalEntry, "stated"> & { forms?: Stated[] }) | undefined => {
    const text = node.getText(node.getSourceFile()).trim();
    const entry = globalEntry(context.overlay, name, member, signature => signature === text,
      declarationOrigin(node.getSourceFile(), context.libraryFile));
    if (!entry) throw Error(`${what} is not in the reviewed overlay of library globals: ${text}`);
    for (const definition of entry.definitions ?? []) context.define(definition);
    const { stated: written, ...rest } = entry;
    const stated = typeof written === "function" ? written(context.library) : written;
    if (stated === undefined) return rest;
    const forms = Array.isArray(stated) ? stated : [stated];
    const [first] = forms;
    if (!first) throw Error(`${what} states an empty list of forms`);
    if (forms.some(f => JSON.stringify(f.binders) !== JSON.stringify(first.binders)))
      throw Error(`${what} states forms under different binders`);
    return { ...rest, forms };
  };
  const reviewed = (member: string | undefined, node: Node, what: string):
      (Omit<GlobalEntry, "stated"> & { stated?: Stated }) | undefined => {
    const entry = reviewedForms(member, node, what);
    if (!entry) return undefined;
    const { forms, ...rest } = entry;
    if (forms && forms.length > 1) throw Error(`${what} states several forms, read only as construct signatures`);
    return { ...rest, ...(forms?.[0] ? { stated: forms[0] } : {}) };
  };
  // The interface the variable is annotated with, a plain or qualified name.
  const annotation = declaration.type;
  const written = annotation && ts.isTypeReferenceNode(annotation)
    ? ts.isQualifiedName(annotation.typeName) ? annotation.typeName.right : annotation.typeName : null;
  const holder = written && ts.isIdentifier(written) ? context.lookup(written, where(declaration, written.text)) : null;
  if (!holder || !ts.isInterfaceDeclaration(holder) || holder.typeParameters?.length)
    throw Error(`the global ${name} is not annotated with a non-generic interface`);
  const parts = context.partners.get(holder) ?? [holder];
  // A member's declaration is read in its own interface: the variable's, or
  // a base TypeScript found it in, which must bind no type parameters.
  const scopeOf = (member: Node, what: string): TermScope => {
    const owner = member.parent;
    if (!ts.isInterfaceDeclaration(owner)) throw Error(`${what} is not an interface member`);
    if (!parts.includes(owner) && owner.typeParameters?.length)
      throw Error(`${what} is inherited from a generic interface`);
    return context.valueScope(member, what);
  };
  // The declaration among `candidates` TypeScript resolves `call` to.
  const resolvedAmong = <T extends Node>(call: ts.CallExpression | ts.NewExpression, candidates: readonly T[]):
      T | undefined => {
    const resolved = checker.getResolvedSignature(call)?.declaration?.resolve();
    return candidates.find(m => resolved && m.pos === resolved.pos && m.end === resolved.end &&
      m.getSourceFile().fileName === resolved.getSourceFile().fileName);
  };
  // A method's or call signature's forms. A parameter the overlay restricts
  // is stated at what the host accepts: its safe part.
  const forms = (signature: ts.MethodSignatureDeclaration | ts.CallSignatureDeclaration, key: string,
      what: string, entry: GlobalEntry | undefined) => {
    if (signature.typeParameters?.length || (ts.isMethodSignatureDeclaration(signature) &&
        (signature.postfixToken || signature.modifiers?.length)))
      throw Error(`${what} is generic, optional or modified`);
    context.clean(signature, where(signature, key));
    const at = spanOf(signature);
    // `this` as the result is the host: the variable, at this definition.
    const self: TypeTerm = { k: "self", span: at };
    const given = signature.type?.kind === ts.SyntaxKind.ThisType ? self : undefined;
    const read = signatures(scopeOf(signature, what), signature.parameters, signature.type, signature, at, false,
      given).map(form => ({ ...form, effect: entry?.effect ?? form.effect }));
    const admit = entry?.admit;
    if (!admit) return read;
    const index = signature.parameters.findIndex(p => ts.isIdentifier(p.name) && p.name.text === admit.parameter);
    const parameter = signature.parameters[index];
    if (!parameter || parameter.dotDotDotToken) throw Error(`${what} has no parameter ${admit.parameter}`);
    const stated: TypeTerm[] = admit.safe.map(atom => ({ k: "atom", name: atom, span: at }));
    if (parameter.questionToken && !admit.safe.includes("undefined"))
      stated.push({ k: "atom", name: "undefined", span: at });
    const [only] = stated;
    const type: TypeTerm = stated.length === 1 && only ? only : { k: "union", parts: stated, span: at };
    return read.map(form => ({ ...form, params: form.params.map((p, i) => i === index ? type : p) }));
  };
  const type = checker.getTypeAtLocation(first);
  if (!type) throw Error(`TypeScript gives ${name} no type`);
  const keys = new Map<string, ts.PropertyAccessExpression[]>();
  const calls: ts.CallExpression[] = [];
  const constructs: ts.NewExpression[] = [];
  // References reading the global as a value, `xs.filter(Boolean)`.
  const valueUses: Identifier[] = [];
  for (const use of uses) {
    const parent = use.parent;
    if (ts.isPropertyAccessExpression(parent) && parent.expression === use && !parent.questionDotToken &&
        ts.isIdentifier(parent.name))
      keys.set(parent.name.text, [...keys.get(parent.name.text) ?? [], parent]);
    else if (ts.isCallExpression(parent) && parent.expression === use && !parent.questionDotToken)
      calls.push(parent);
    else if (ts.isNewExpression(parent) && parent.expression === use)
      constructs.push(parent);
    else if (ts.isBinaryExpression(parent) && parent.right === use &&
        parent.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) {
      // `e instanceof X`, read only where the overlay states it as a test of
      // the calculus, against the variable's declaration as reviewed.
      const entry = reviewed(undefined, declaration, `${name} as the right operand of instanceof`);
      // A test of the calculus, or an intrinsic stating the Boolean alone.
      if (entry?.intrinsic) context.intrinsic(spanOf(parent), entry.intrinsic);
      else if (entry?.test) context.test(spanOf(parent), entry.test);
      else throw Error(`${name} is not read as an instanceof test`);
    }
    else if (isWritten(use)) throw Error(`the global ${name} is written, which the module may not do`);
    else valueUses.push(use);
  }
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const [key, accesses] of keys) {
    const what = `${name}.${key}`;
    const nodes = (checker.getPropertyOfType(type, key)?.declarations ?? []).map(d => d.resolve());
    const methods = nodes.filter((d): d is ts.MethodSignatureDeclaration => !!d && ts.isMethodSignatureDeclaration(d));
    const [property] = nodes;
    if (methods.length && methods.length === nodes.length) {
      const chosen = new Map<ts.MethodSignatureDeclaration, ts.CallExpression[]>();
      for (const access of accesses) {
        const call = access.parent;
        if (!ts.isCallExpression(call) || call.expression !== access || call.questionDotToken)
          throw Error(`the method ${what} is only called, on its host`);
        const overload = resolvedAmong(call, methods);
        if (!overload) throw Error(`TypeScript resolves the call of ${what} to no overload it declares`);
        chosen.set(overload, [...chosen.get(overload) ?? [], call]);
      }
      const selected = [...chosen].flatMap(([overload, calls]) => {
        const entry = reviewed(key, overload, what);
        // A test of the calculus: each call is reported, and the member
        // joins no value.
        if (entry?.test) {
          for (const call of calls) {
            const [argument, ...more] = call.arguments;
            if (!argument || more.length || ts.isSpreadElement(argument) || call.typeArguments?.length)
              throw Error(`${what} is a test of one argument`);
            context.test(spanOf(call), entry.test);
          }
          return [];
        }
        // A call of an intrinsic stating the same step: each call is
        // reported, with its arguments as written, and the member joins no
        // value. Explicit type arguments are TypeScript's instance of the
        // declaration; the intrinsic's is proposed and checked on its own.
        if (entry?.intrinsic) {
          for (const call of calls) {
            if (call.arguments.some(ts.isSpreadElement))
              throw Error(`${what} is read as an intrinsic, called without spreads`);
            context.intrinsic(spanOf(call), entry.intrinsic);
          }
          return [];
        }
        // A signature the overlay states instead of the declared one: its
        // parameters bound the arguments, as for a construct.
        if (entry?.stated) {
          const stated = entry.stated;
          for (const call of calls) boundedArguments(call, stated, what);
          const at = spanOf(overload);
          const form: FunctionTerm = { k: "function", effect: entry.effect ?? ordinaryEffect, receiver: { k: "self", span: at }, params: stated.params,
            rest: stated.rest ?? null, result: stated.result, span: at };
          // A generic statement is a scheme over its binders, as a generic
          // interface method is.
          return [stated.binders.length
            ? { k: "scheme", binders: stated.binders.map(name => ({ name, bound: null, resolution: null, default: null, span: at })),
                signatures: [form], span: at } satisfies TypeTerm
            : form];
        }
        return forms(overload, key, what, entry).map(form => {
          if (form.receiver) throw Error(`the method ${what} states its receiver`);
          return { ...form, receiver: { k: "self", span: form.span } satisfies TypeTerm };
        });
      });
      if (!selected.length) continue;
      const [only] = selected;
      const span = spanOf(accesses[0] ?? first);
      // A generic member is a readonly scheme, and overloads none.
      const scheme = selected.some(form => form.k === "scheme");
      if (scheme && selected.length > 1) throw Error(`${what} selects a generic statement beside other overloads`);
      // A reviewed method is readonly: neither the global nor a value its
      // methods return as the receiver (`process.on(…)`) admits replacing it.
      fields.push({ name: key, optional: false, readonly: true, span,
        type: selected.length === 1 && only ? only : { k: "intersection", parts: selected, span } });
    } else if (nodes.length === 1 && property && ts.isPropertySignatureDeclaration(property) && property.type &&
        !property.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword)) {
      const entry = reviewed(key, property, what);
      context.clean(property, where(property, key));
      // A member read at a stated contract is a readonly view: no write of
      // it is admitted.
      fields.push({ name: key, optional: property.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
        readonly: !!entry?.stated || property.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
        type: entry?.stated ? entry.stated.result : typeTerm(scopeOf(property, what), property.type, property),
        span: spanOf(property) });
    } else throw Error(`${what} is not one property signature or method signatures`);
  }
  // The call signatures the client's calls of the global resolve to, each
  // once, with the calls that chose it.
  const declared = parts.filter(ts.isInterfaceDeclaration)
    .flatMap(part => part.members.filter(ts.isCallSignatureDeclaration));
  const chosen = new Map<ts.CallSignatureDeclaration, ts.CallExpression[]>();
  for (const call of calls) {
    const signature = resolvedAmong(call, declared);
    if (!signature) throw Error(`TypeScript resolves the call of ${name} to no call signature it declares`);
    chosen.set(signature, [...chosen.get(signature) ?? [], call]);
  }
  // A value is every call signature: whoever receives it may call any. A
  // standard library global is read as one only where the overlay states
  // each for it (`value`).
  if (valueUses.length) {
    if (!declared.length) throw Error(`${name} is read as a value, which declares no call signature`);
    for (const signature of declared) {
      if (!reviewed(undefined, signature, `${name} as a value`)?.value)
        throw Error(`${name} is read as a value only where the overlay states its call signatures for one`);
      if (!chosen.has(signature)) chosen.set(signature, []);
    }
  }
  const what = `${name}(…)`;
  // A call the overlay reads as the global's construct, `Error(m)`: each is
  // reported, and its statement joins the construct signatures.
  const calledConstructs: { binders: string[]; type: TypeTerm }[] = [];
  const callForms = [...chosen].flatMap(([signature, calls]) => {
    const entry = reviewed(undefined, signature, what);
    if (entry?.construct) {
      const stated = entry.stated;
      if (!stated) throw Error(`${what} is read as a construct with no statement`);
      for (const call of calls) {
        if (call.arguments.length > stated.params.length || call.arguments.some(ts.isSpreadElement))
          throw Error(`${what} is read with at most ${stated.params.length} argument(s)`);
        context.construct(spanOf(call));
      }
      calledConstructs.push({ binders: stated.binders, type: { k: "constructor", effect: entry.effect ?? ordinaryEffect,
        params: stated.params, rest: null, result: stated.result, span: spanOf(signature) } });
      return [];
    }
    // A call signature the overlay states instead of the declared one, as a
    // member's: its parameters bound the arguments.
    if (entry?.stated) {
      const stated = entry.stated;
      if (stated.binders.length) throw Error(`${what} is stated with binders, which a call signature cannot hold`);
      for (const call of calls) boundedArguments(call, stated, what);
      const at = spanOf(signature);
      return [{ k: "function", effect: entry.effect ?? ordinaryEffect, receiver: null, params: stated.params,
        rest: stated.rest ?? null, result: stated.result, span: at } satisfies FunctionTerm];
    }
    return forms(signature, name, what, entry).map(form => {
      if (form.receiver) throw Error(`${what} states its receiver`);
      return form;
    });
  });
  // The construct signatures the client's `new` expressions resolve to, each
  // read as the overlay states it (`stated`), or, outside the standard
  // library, as declared. A stated signature's parameters bound the
  // arguments: the host is stated only at those.
  const declaredNew = parts.filter(ts.isInterfaceDeclaration)
    .flatMap(part => part.members.filter(ts.isConstructSignatureDeclaration));
  const built = new Map<ts.ConstructSignatureDeclaration, ts.NewExpression[]>();
  for (const expression of constructs) {
    const signature = resolvedAmong(expression, declaredNew);
    if (!signature) throw Error(`TypeScript resolves \`new ${name}\` to no construct signature it declares`);
    built.set(signature, [...built.get(signature) ?? [], expression]);
  }
  const whatNew = `new ${name}(…)`;
  const constructForms = [...calledConstructs, ...[...built].flatMap(([signature, expressions]) => {
    const entry = reviewedForms(undefined, signature, whatNew);
    const span = spanOf(signature);
    // A construct of an intrinsic stating the same step, `new Promise(e)`:
    // each is reported, with its arguments as written, and joins no value.
    if (entry?.intrinsic) {
      for (const expression of expressions) {
        if (expression.arguments?.some(ts.isSpreadElement))
          throw Error(`${whatNew} is read as an intrinsic, constructed without spreads`);
        context.intrinsic(spanOf(expression), entry.intrinsic);
      }
      return [];
    }
    if (entry?.forms) {
      const forms = entry.forms;
      const most = Math.max(...forms.map(f => f.params.length));
      for (const expression of expressions)
        if ((expression.arguments?.length ?? 0) > most || expression.arguments?.some(ts.isSpreadElement))
          throw Error(`${whatNew} is read with at most ${most} argument(s)`);
      return forms.map(stated => ({ binders: stated.binders,
        type: { k: "constructor", effect: entry.effect ?? ordinaryEffect, params: stated.params, rest: null,
          result: stated.result, span } satisfies TypeTerm }));
    }
    if (signature.typeParameters?.length) throw Error(`${whatNew} is generic`);
    context.clean(signature, where(signature, name));
    return signatures(scopeOf(signature, whatNew), signature.parameters, signature.type, signature, span, false)
      .map(form => {
        if (form.receiver) throw Error(`${whatNew} states its receiver`);
        const binders: string[] = [];
        return { binders,
          type: { k: "constructor", effect: form.effect, params: form.params, rest: form.rest, result: form.result,
            span } satisfies TypeTerm };
      });
  })];
  if (valueUses.length && constructForms.length)
    throw Error(`${name} is both constructed and read as a value`);
  const source = declaration.getSourceFile();
  const identity: DeclarationIdentity = { module: context.identityOf(source), name,
    span: [declaration.getStart(source), declaration.end] };
  if (constructForms.length) {
    if (fields.length || callForms.length)
      throw Error(`${name} is both constructed and read through its members or calls`);
    // Overloads the overlay states alike are one signature.
    const distinct = [...new Map(constructForms.map(f =>
      [JSON.stringify({ ...f, type: { ...f.type, span: null } }), f])).values()];
    const [only] = distinct;
    if (distinct.length === 1 && only)
      return { construct: { declaration: identity, typeParams: only.binders.map(name => ({ name, bound: null, resolution: null })),
        type: only.type } };
    // Several signatures under the same binders are one generic class's,
    // every instance meeting each; under different ones they are refused.
    const binders = only?.binders ?? [];
    if (distinct.some(f => JSON.stringify(f.binders) !== JSON.stringify(binders)))
      throw Error(`${whatNew} selects several signatures under different binders`);
    const span = spanOf(first);
    return { construct: { declaration: identity, typeParams: binders.map(name => ({ name, bound: null, resolution: null })),
      type: { k: "intersection", parts: distinct.map(f => f.type), span } } };
  }
  // A global read only through tests is not a value.
  if (!fields.length && !callForms.length) return null;
  return { definition: { declaration: identity, parameters: [], bases: [],
    expression: { k: "object", fields, stringIndex: null, calls: callForms, span: spanOf(first) } } };
}

/** The errors TypeScript reports in `file` itself, in its configured project:
 * what attributes a failed search to code TypeScript refuses too. Display
 * only; never a premise of acceptance. */
export function clientErrors(file: string, tsconfigPath?: string): SeenDiagnostic[] {
  const clientFile = resolve(file);
  return withProject(clientFile, tsconfigPath, (_checker, client, _root, program) =>
    [...program.getSyntacticDiagnostics(client.fileName), ...program.getSemanticDiagnostics(client.fileName)]
      .filter(d => d.category === DiagnosticCategory.Error)
      .map(d => ({ file: client.fileName, client: true, pos: [d.pos, d.end],
        start: client.getLineAndCharacterOfPosition(d.pos),
        end: client.getLineAndCharacterOfPosition(d.end), text: d.text })));
}

/** A merged interface's body: every part's fields, calls and at most one
 * string index, with no field named twice. The first part's span stands for
 * the whole. */
function mergeMembers(parts: TypeTerm[], fail: (at: Node, message: string) => never, at: Node): TypeTerm {
  const [first, ...rest] = parts;
  // One declaration of construct signatures only is its constructor type.
  if (first && !rest.length && (first.k === "constructor" || first.k === "intersection")) return first;
  if (!first || first.k !== "object") return fail(at, "an interface body is a record");
  if (!rest.length) return first;
  const fields = [...first.fields];
  let stringIndex = first.stringIndex;
  let numberIndex = first.numberIndex;
  let symbolIndex = first.symbolIndex;
  const calls = [...first.calls];
  const key = (name: PropertyKey) => typeof name === "string" ? name : `[symbol ${name.symbol}]`;
  for (const part of rest) {
    if (part.k !== "object") return fail(at, "an interface body is a record");
    for (const field of part.fields) {
      if (fields.some(f => key(f.name) === key(field.name)))
        fail(at, "a merged interface declares a member twice");
      fields.push(field);
    }
    if (part.stringIndex) {
      if (stringIndex) fail(at, "a merged interface declares two string index signatures");
      stringIndex = part.stringIndex;
    }
    if (part.numberIndex) {
      if (numberIndex) fail(at, "a merged interface declares two number index signatures");
      numberIndex = part.numberIndex;
    }
    if (part.symbolIndex) {
      if (symbolIndex) fail(at, "a merged interface declares two symbol index signatures");
      symbolIndex = part.symbolIndex;
    }
    calls.push(...part.calls);
  }
  return { ...first, fields, stringIndex, ...(numberIndex ? { numberIndex } : {}),
    ...(symbolIndex ? { symbolIndex } : {}), calls };
}

/** A class's instance contract merged with its interfaces' members, as
 * TypeScript merges them: a property both declare is one, of the one type
 * TypeScript requires of both; a method both declare would be overloads,
 * outside the fragment. The class's constructor must establish the whole
 * contract, checked where the class is defined in the checked module; an
 * imported class's constructor is a trusted declaration. */
function mergedClass(instance: TypeTerm, interfaces: TypeTerm[], fail: (at: Node, message: string) => never,
    at: Node): TypeTerm {
  if (!interfaces.length) return instance;
  if (instance.k !== "object") return fail(at, "a class merged with an interface states no record");
  const key = (name: PropertyKey) => typeof name === "string" ? name : `[symbol ${name.symbol}]`;
  const own = new Set(instance.fields.map(f => key(f.name)));
  const added = interfaces.map(part => {
    if (part.k !== "object") return fail(at, "an interface merged with a class is a record");
    for (const field of part.fields)
      if (own.has(key(field.name)) &&
          (field.type.k === "function" || field.type.k === "scheme" || field.type.k === "intersection"))
        fail(at, "a method a class and an interface merged with it both declare would be overloads, outside the fragment");
    return { ...part, fields: part.fields.filter(f => !own.has(key(f.name))) };
  });
  return mergeMembers([instance, ...added], fail, at);
}

/** A standard library interface through its overlay entries
 * (`interfaceOverlay`): each listed member, read from the one declaration
 * among the merged parts whose text is the reviewed one, a method as a
 * host-relative member and a property as declared. A member the project's
 * library does not declare is left out. */
function overlaidInterface(node: InterfaceDeclaration, parts: readonly InterfaceDeclaration[],
    entries: readonly OverlayEntry[], scopeOf: (part: InterfaceDeclaration) => TermScope,
    identityOf: (node: TypeDeclaration) => DeclarationIdentity,
    symbol: (written: Identifier | ts.PropertyAccessExpression) => number,
    library: (name: string, span: Span) => (args: TypeTerm[]) => TypeTerm): TypeTerm {
  const where = `${identityOf(node).module}#${node.name.text}`;
  const keyText = (member: ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration,
      source: SourceFile): string =>
    ts.isIdentifier(member.name) ? member.name.text : member.name.getText(source);
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const entry of entries) {
    const named = parts.flatMap(part => {
      const source = part.getSourceFile();
      return part.members
        .filter((m): m is ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration =>
          (ts.isMethodSignatureDeclaration(m) || ts.isPropertySignatureDeclaration(m)) &&
          keyText(m, source) === entry.name)
        .map(member => ({ member, source, part }));
    });
    if (!named.length) continue;
    const found = named.filter(({ member, source }) => member.getText(source).trim() === entry.signature);
    const [only, ...more] = found;
    if (!only || more.length) throw Error(`${where}.${entry.name} is not declared as reviewed: ${entry.signature}`);
    const { member, source, part } = only;
    const scope = scopeOf(part);
    const span: Span = [member.getStart(source), member.end];
    const name = member.name;
    const key: PropertyKey = ts.isComputedPropertyName(name) &&
        (ts.isPropertyAccessExpression(name.expression) || ts.isIdentifier(name.expression))
      ? { symbol: symbol(name.expression) } : entry.name;
    if (ts.isPropertySignatureDeclaration(member)) {
      if (!member.type || member.postfixToken ||
          member.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword))
        throw Error(`${where}.${entry.name} is not a plain property`);
      fields.push({ name: key, optional: false, readonly: !!member.modifiers?.length,
        type: typeTerm(scope, member.type, member), span });
      continue;
    }
    if (!ts.isMethodSignatureDeclaration(member) || member.typeParameters?.length || member.postfixToken)
      throw Error(`${where}.${entry.name} is not a plain method`);
    const nameOf = (p: ts.ParameterDeclaration) => ts.isIdentifier(p.name) ? p.name.text : "";
    const parameters = member.parameters.filter(p => !entry.drop?.includes(nameOf(p)));
    // The weaker result: `Iterator` at the declared result's one argument.
    let given: TypeTerm | undefined;
    if (entry.resultAs) {
      const declared = member.type;
      const [argument, ...others] = declared && ts.isTypeReferenceNode(declared) ? declared.typeArguments ?? [] : [];
      if (!argument || others.length) throw Error(`${where}.${entry.name} has no element type to state`);
      given = library(entry.resultAs, span)([typeTerm(scope, argument, member)]);
    } else if (entry.resultIsReceiver) {
      if (member.type?.kind !== ts.SyntaxKind.ThisType) throw Error(`${where}.${entry.name} does not return this`);
      given = { k: "self", span };
    }
    const forms = signatures(scope, parameters, member.type, member, span, false, given);
    if (forms.some(f => f.receiver)) throw Error(`${where}.${entry.name} states its receiver`);
    fields.push({ name: key, optional: false, readonly: false, span,
      type: oneTerm(forms.map(f => ({ ...f, receiver: { k: "self", span }, effect: entry.effect ?? f.effect })), span) });
  }
  return { k: "object", fields, stringIndex: null, calls: [], span: identityOf(node).span };
}

/** Every declaration reachable from `start`, each once across roots. */
/** The standard library's iterator interfaces ECMA-262 specifies, whose
 * done value `BuiltinIteratorReturn` names. */
const ecmaIterators = ["ArrayIterator", "MapIterator", "SetIterator", "StringIterator", "RegExpStringIterator"];

type DeclarationInstance = { identity: DeclarationIdentity; args: readonly TypeTerm[]; use: Node };

function collect(start: TypeDeclaration, seen: Set<string>, definitions: TypeDefinition[], context: {
  diagnostic: ((identity: DeclarationIdentity, reason: string) => void) | undefined;
  lookup: (identifier: Identifier, what: string) => TypeDeclaration;
  computedMembers: (node: TypeDeclaration) => boolean;
  instanceOf: (node: TypeDeclaration, args: readonly TypeTerm[], use: Node, span: Span) => TypeTerm;
  instantiate: (node: Node, args: readonly TypeTerm[], use: Node | null) => (part: TypeNode) => TypeTerm;
  identityOf: (node: TypeDeclaration) => DeclarationIdentity;
  /** Whether an identity is a branded string of the host (reading rule 5). */
  isBrand: (id: DeclarationIdentity) => boolean;
  /** Whether a file is the standard library's (`moduleIds`). */
  libraryFile: (file: SourceFile) => boolean;
  /** Whether a declaration is a host type, whose members are readonly views. */
  hostType: (node: TypeDeclaration) => boolean;
  symbol: (written: Identifier | ts.PropertyAccessExpression) => number;
  literalKey: (written: Identifier | ts.PropertyAccessExpression) => string | null;
  privateName: (name: ts.PrivateIdentifier) => number;
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>;
  library: (identifier: Identifier, what: string) => LibraryType | null;
  /** A declaration's equation where it is not its declared body. */
  equation: (node: TypeDeclaration) => TypeTerm | null;
  /** The standard library interface of this name, such as `Iterator`. */
  libraryInterface: (name: string) => TypeDeclaration;
  /** The native collection iterator over an element type. */
  collectionIterator: (element: TypeTerm) => TypeTerm;
  /** A computed type's term (`computed-types.mts`). */
  computed: NonNullable<TermScope["computed"]>;
  /** The type alias a reference names, if any. */
  alias: (reference: ts.TypeReferenceNode) => TypeAliasDeclaration | null;
  awaited: NonNullable<TermScope["awaited"]>;
  /** Whether a reference is a statement (`Within`), recording that the
   * definition `owner` reads one. */
  stated: (reference: ts.TypeReferenceNode, owner: string) => boolean;
  /** Told each declaration collected, under its key, before its equation
   * is read, and null once collection ends: the program's classes and the
   * definitions reading a statement are recorded (`externalStatements`). */
  collecting: (node: TypeDeclaration | null, key: string | null) => void;
  /** A mapped type's keys as TypeScript computes them. */
  keys: NonNullable<TermScope["keys"]>;
  /** Told each definition that is a record written as one (`NamedRecords`). */
  record: (identity: DeclarationIdentity) => void;
  /** A mapped type over `keyof` as TypeScript resolves it. */
  modifiers: NonNullable<TermScope["modifiers"]>;
  /** A declaration's type parameters, its merged declarations together. */
  parameters: (declaration: Node) => readonly MergedParameter[];
  /** An application's arguments completed with its defaults. */
  complete: (declaration: Node, written: readonly TypeTerm[], use: Node | null, what: string,
    captured?: (parameter: ts.TypeParameterDeclaration) => TypeTerm) => TypeTerm[];
  /** The type an enum's name denotes where a file writes it, or null for a
   * name that is no enum's. */
  enumType: (identifier: Identifier, at: SourceFile, span: Span) => TypeTerm | null;
  /** An enum member's literal type `E.M`, or `typeof E`. */
  enumerated: NonNullable<TermScope["enumerated"]>;
  /** The name a type reference reads, a namespace member's included. */
  memberName: (name: ts.EntityName) => Identifier | null;
  /** A host family's table and the run's tag selection, where `node` is a
   * declaration of the family. */
  family: (node: InterfaceDeclaration) => { table: FamilyTable; selection: ReadonlySet<TagValue> } | null;
  /** The promises of the listed node guards the run reads, by their
   * families' markers and their definitions' names: each the tag values of
   * its entry. */
  guardPromises: ReadonlyMap<string, ReadonlyMap<string, readonly TagValue[]>>;
}, instance?: DeclarationInstance): void {
  const { lookup, identityOf, symbol, partners, library, equation } = context;
  const queue: TypeDeclaration[] = [start];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const node = queue[cursor];
    if (!node) throw Error("missing queued declaration");
    const applied = cursor === 0 ? instance : undefined;
    const identity = applied?.identity ?? identityOf(node);
    const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    context.collecting(node, key);
    const before = definitions.length;
    const availableBefore = context.diagnostic ? new Set(seen) : null;
    try {
    const stated = equation(node);
    if (stated) {
      definitions.push({ declaration: identity, parameters: [], bases: [], expression: stated });
      continue;
    }
    const source = node.getSourceFile();
    // Its parameters, its merged declarations together.
    // A block type's captured parameters come first; an own parameter
    // shadows a captured one of its spelling (`lastIndexOf`).
    const parameterNodes = context.parameters(node);
    const parameterNames = parameterNodes.map(parameter => parameter.name.text);
    const capturedNames = parameterNodes.filter(p => p.captured).map(p => p.name.text);
    const ownNames = parameterNames.slice(capturedNames.length);
    if (new Set(ownNames).size !== ownNames.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
    // A captured parameter at a reference in the body: this declaration's
    // own position for the same type parameter.
    const capturedHere = (parameter: ts.TypeParameterDeclaration): TypeTerm => {
      const index = parameterNodes.findIndex(p => {
        const at = p.name.parent;
        return !!p.captured && !!at && at.pos === parameter.pos && at.end === parameter.end &&
          at.getSourceFile().fileName === parameter.getSourceFile().fileName;
      });
      if (index < 0) throw Error(`a type declared in a block closes over ${parameter.name.text}, which ${identity.module}#${identity.name} does not`);
      return { k: "parameter", index, span: [parameter.getStart(parameter.getSourceFile()), parameter.end] };
    };
    const reference = (source: SourceFile, identifier: Identifier, arguments_: readonly TypeNode[], pos: Span,
        read: (part: TypeNode) => TypeTerm, base = false, written?: ts.TypeReferenceNode): TypeTerm => {
      const what = `${identity.module}#${identifier.text}`;
      const known = library(identifier, what);
      // A base is a declaration whose members are inherited; a library type
      // read at its meaning has none here. A class extending `Array` has
      // instances that are arrays, exotic objects allocated by the library's
      // constructor, which a class's construction (an ordinary allocation)
      // does not give.
      if (known && base)
        throw Error(`extending the standard library's ${identifier.text} is outside the fragment: ` +
          "its instances are what the library's constructor allocates, not an ordinary object a class allocates, " +
          "and its members are read at the library type's meaning, not inherited");
      if (known) return libraryTerm(known, libraryArguments(known, arguments_, read, context.keys), pos,
        message => { throw Error(`${message} in ${identity.module}#${identity.name}`); });
      const targetNode = lookup(identifier, what);
      // `BuiltinIteratorReturn`, the standard library's `intrinsic` alias, is
      // what an iterator of ECMA-262 returns when it is done: the iterators
      // of arrays, maps, sets, strings and `matchAll` complete with
      // CreateIterResultObject(undefined, true), so in their interfaces it
      // is `undefined`, as `strictBuiltinIteratorReturn` reads it. Another
      // interface naming it (Intl's, the DOM's) is another specification's
      // iterator, which this reading does not attribute.
      if (ts.isTypeAliasDeclaration(targetNode) && targetNode.name.text === "BuiltinIteratorReturn" &&
          context.libraryFile(targetNode.getSourceFile())) {
        const owner = ts.isInterfaceDeclaration(node) ? node.name.text : "";
        if (context.libraryFile(source) && ecmaIterators.includes(owner))
          return { k: "atom", name: "undefined", span: pos };
        throw Error(`BuiltinIteratorReturn in ${identity.module}#${identity.name} is the done value of an iterator ECMA-262 does not specify; only ${ecmaIterators.join(", ")} are read`);
      }
      // An alias TypeScript computes from its parameters is the type it
      // computes at this reference's arguments.
      if (written && computedAlias(targetNode, context.alias)) return computed(written, pos, read);
      const target = identityOf(targetNode);
      const completed = context.complete(targetNode, arguments_.map(read), written ?? null,
        `${target.module}#${target.name}`, capturedHere);
      if (context.computedMembers(targetNode)) {
        if (!written) throw Error(`${identifier.text}: computed members need a written type application`);
        return context.instanceOf(targetNode, completed, written, pos);
      }
      const edge: Reference = { name: identifier.text, span: pos,
        arguments: arguments_.map(arg => [arg.getStart(source), arg.end]), target };
      queue.push(targetNode);
      return { k: "reference", reference: edge, args: completed, span: pos };
    };
    // Each declaration part is read in its own file, which its spans index.
    let body: TypeNode | undefined;
    if (ts.isTypeAliasDeclaration(node)) {
      body = node.type;
      while (ts.isParenthesizedTypeNode(body)) body = body.type;
    }
    // A declaration's own parameters are positional: a computed type that
    // reaches a function's binder has no reading in its equation.
    const computed: NonNullable<TermScope["computed"]> = (part, pos, read) => {
      const term = applied ? context.instantiate(node, applied.args, applied.use)(part) : context.computed(part, pos, read);
      if (JSON.stringify(term).includes('"k":"binder"'))
        throw Error(`${computedForm(part) ?? "a computed alias"} reaches a function's type parameter in ${identity.module}#${identity.name}`);
      return term;
    };
    // A part of a merged interface binds a prefix of the declaration's
    // parameters, by position: its members are read with only those.
    const scopeOf = (source: SourceFile, names: readonly string[] = parameterNames): TermScope => ({
      source,
      annotation: false,
      awaited: context.awaited,
      stated: part => context.stated(part, key),
      ...(body ? { body } : {}),
      symbol,
      literalKey: context.literalKey,
      privateName: context.privateName,
      keys: context.keys,
      modifiers: context.modifiers,
      computed,
      enumerated: context.enumerated,
      fail: (_node, message) => { throw Error(`${message} in ${identity.module}#${identity.name}`); },
      named: (part, pos, read) => {
        const name = context.memberName(part.typeName);
        if (!name) throw Error(`a qualified type reference in ${identity.module}#${identity.name}`);
        const own = ts.isIdentifier(part.typeName) && names.includes(name.text);
        const enumType = own ? null : context.enumType(name, source, pos);
        if (enumType) {
          if (part.typeArguments?.length) throw Error(`an enum type takes no type arguments: ${name.text}`);
          return enumType;
        }
        const index = own ? names.lastIndexOf(name.text) : -1;
        if (index < 0) return reference(source, name, part.typeArguments ?? [], pos, read, false, part);
        if (part.typeArguments?.length)
          throw Error(`type parameter applied as constructor: ${name.text}`);
        return applied?.args[index] ?? { k: "parameter", index, span: pos };
      },
    });
    const scope = scopeOf(source);
    const parts = partners.get(node) ?? [node];
    const partScope = (part: TypeDeclaration): TermScope =>
      scopeOf(part.getSourceFile(), [...capturedNames, ...(part.typeParameters ?? []).map(parameter => parameter.name.text)]);
    // A bound or default is read in the scope of the declaration stating it.
    const statedIn = (at: { part: TypeDeclaration; type: TypeNode | undefined }): TypeTerm | null =>
      at.type ? typeTerm(partScope(at.part), at.type) : null;
    let sawDefault = false;
    const parameters = applied ? [] : parameterNodes.map((parameter, index) => {
      if (sawDefault && !parameter.default)
        throw Error(`required type parameter after default in ${identity.module}#${identity.name}`);
      sawDefault ||= !!parameter.default;
      const own = (parameter.captured ? undefined : node.typeParameters?.[index - capturedNames.length]) ??
        parameter.name.parent;
      const parameterSpan: Span = [own.getStart(own.getSourceFile()), own.end];
      return { name: parameter.name.text, span: parameterSpan, defaulted: !!parameter.default };
    });
    // An alias TypeScript computes from its parameters has no equation: its
    // definition states its parameters and defaults.
    // (A predicate's false branch would narrow `node` to no alias.)
    const computedEquation: boolean = computedAlias(node, context.alias);
    if (computedEquation || (!applied && context.computedMembers(node))) {
      definitions.push({ declaration: identity, parameters, bases: [], expression: null });
      continue;
    }
    // A standard library interface read through the overlay: only its listed
    // members, and no base.
    const overlaid = ts.isInterfaceDeclaration(node) && Object.hasOwn(interfaceOverlay, node.name.text) &&
        parts.every(part => context.libraryFile(part.getSourceFile()))
      ? interfaceOverlay[node.name.text] : undefined;
    if (overlaid && ts.isInterfaceDeclaration(node)) {
      definitions.push({ declaration: identity, parameters, bases: [],
        expression: overlaidInterface(node, parts.filter(ts.isInterfaceDeclaration), overlaid, partScope,
          identityOf, symbol, (name, span) => {
          if (name === "NativeIterator") return ([element]: TypeTerm[]): TypeTerm => {
            if (!element) throw Error("a collection iterator states its element");
            return context.collectionIterator(element);
          };
          const target = context.libraryInterface(name);
          queue.push(target);
          return (args: TypeTerm[]): TypeTerm => ({ k: "reference", span,
            args: context.complete(target, args, null, name),
            reference: { name, span, arguments: args.map(() => span), target: identityOf(target) } });
        }) });
      continue;
    }
    // A host class, and a host interface the contract names a view for, is
    // read through its named view (reading rule 4): the members the contract
    // lists, each as its reviewed text declares it.
    const named = compilerApiFile(source.fileName) ? hostViews.find(v => v.owner === node.name?.text) : undefined;
    const view = ts.isClassDeclaration(node) && compilerApiFile(source.fileName) ? named?.members ?? []
      : ts.isInterfaceDeclaration(node) ? named?.members ?? null : null;
    if (view && (ts.isClassDeclaration(node) || ts.isInterfaceDeclaration(node)))
      for (const entry of view)
        if (!parts.some(part => (ts.isClassDeclaration(part) || ts.isInterfaceDeclaration(part)) &&
            part.members.some((m: Node) => m.getText(part.getSourceFile()).trim() === entry.text)))
          throw Error(`${node.name?.text}.${entry.name} is not declared as reviewed: ${entry.text}`);
    const admitted = (member: Node): boolean =>
      !view || view.some(entry => member.getText(member.getSourceFile()).trim() === entry.text);
    // A view is the whole shape: no declaration outside the audited
    // installation merges into it, and it inherits nothing.
    if ((view || context.hostType(node)) && parts.some(part => !isHostFile(part.getSourceFile().fileName)))
      throw Error(`a declaration merged into the host type ${node.name?.text} outside the audited installation is refused: the installation's declarations are its whole shape (COMPILER-API.md, reading rules 1 and 4)`);
    // A declaration of a host family (HOST-FAMILIES.md, "The family
    // contract"): one whose tag is a set of literals, or a generic one, is
    // its flattened members with the family's marker; one whose tag is no
    // set of literals keeps its identity and is read as the union of the
    // arms the run's selection keeps, the residual last.
    const familyReading = ts.isInterfaceDeclaration(node) ? context.family(node) : null;
    if (familyReading && ts.isInterfaceDeclaration(node)) {
      const { table, selection } = familyReading;
      const marker = table.description.marker;
      const span: Span = [node.getStart(source), node.end];
      const tagTerm = (values: readonly TagValue[]): TypeTerm => {
        const parts = values.map(v => literalTerm(v, span));
        const [only] = parts;
        return only && parts.length === 1 ? only : { k: "union", parts, span };
      };
      // A flattened member, read in its owner's scope, as a host type's
      // member is (reading rules 1, 2 and 5), optional where it is at one of
      // the tags `tags` the reading covers; a generic owner's tag parameter
      // is read at `value` where a synthetic shape reads it.
      type Field = Extract<TypeTerm, { k: "object" }>["fields"][number];
      const readMember = (f: FlatMember, tags: readonly TagValue[], value: TagValue | null): Field => {
        const file = f.owner.getSourceFile();
        const names = (f.owner.typeParameters ?? []).map(p => p.name.text);
        const term = members(scopeOf(file, names), f.members, f.owner, [f.owner.getStart(file), f.owner.end], true);
        const [field] = term.k === "object" ? term.fields : [];
        if (term.k !== "object" || !field || term.fields.length !== 1 || term.calls.length || term.stringIndex)
          throw Error(`the family ${marker} reads ${f.owner.name.text}.${f.name} as no one member`);
        const substituted = names.length && value !== null ? substitute(field.type, [literalTerm(value, span)]) : field.type;
        // A method the family states a footprint for, its text reviewed
        // (`familyTable`), is read at it (T3).
        const stated = table.description.footprints.find(m => m.owner === f.owner.name.text && m.member === f.name);
        const type = stated ? footprintReading(stated.kind, substituted) : substituted;
        return { ...field, readonly: true,
          optional: field.optional || table.optional(f, tags) || f.members.some(readsAsOptionalUnknown),
          type: hostBrands(type, true, context.isBrand,
            message => { throw Error(`${message} in ${identity.module}#${identity.name}.${f.name}`); }) };
      };
      // A shape's stable members: its property members, required or
      // optional, the stable-member rule names, the tag among them
      // (HOST-FAMILIES.md, "Stable keys").
      const shape = (fields: Field[], stable: readonly string[]): TypeTerm => {
        const keys = fields.flatMap(f => typeof f.name === "string" && stable.includes(f.name) ? [f.name] : []);
        return { k: "object", fields, stringIndex: null, calls: [], span, host: marker, ...(keys.length ? { stable: keys } : {}) };
      };
      const reference = (target: TypeDeclaration, args: TypeTerm[]): TypeTerm => {
        queue.push(target);
        const id = identityOf(target);
        return { k: "reference", span, args: context.complete(target, args, null, `${id.module}#${id.name}`),
          reference: { name: id.name, span, arguments: args.map(() => span), target: id } };
      };
      const synthetic = (name: string): { id: DeclarationIdentity; fresh: boolean; term: TypeTerm } => {
        const id: DeclarationIdentity = { module: `tscert/family/${marker}`, name, span: [0, 0] };
        const key = `${id.module}#${id.name}`;
        const fresh = !seen.has(key);
        seen.add(key);
        return { id, fresh, term: { k: "reference", span, args: [], reference: { name, span, arguments: [], target: id } } };
      };
      // Each method a declaration states is one definition, which every
      // shape stating it required names as a base: one method head, shared
      // by the shapes, whatever other methods a shape overrides. A method a
      // shape states optional, by its declaration or by a correction of the
      // shape's tag, is that shape's own optional member.
      const isMethod = (f: FlatMember): boolean => f.members.every(ts.isMethodSignatureDeclaration);
      const shared = (f: FlatMember, tags: readonly TagValue[]): boolean => isMethod(f) && !table.optional(f, tags);
      const methodBase = (f: FlatMember): TypeTerm => {
        const made = synthetic(`${f.owner.name.text}.${f.name}`);
        if (made.fresh) {
          if (f.owner.typeParameters?.length) throw Error(`the family ${marker} reads no methods of the generic ${f.owner.name.text}`);
          definitions.push({ declaration: made.id, parameters: [], bases: [], expression: { k: "object",
            fields: [readMember(f, [], null)], stringIndex: null, calls: [], span } });
        }
        return made.term;
      };
      const methodOwners = (methods: readonly FlatMember[]): TypeTerm[] => methods.map(methodBase);
      // A term without its spans, which two readings of one member share.
      const unspanned = (t: TypeTerm): string =>
        JSON.stringify(t, (key: string, v: unknown): unknown => key === "span" || key === "arguments" ? undefined : v) ?? "";
      const arm = (a: FamilyArm): TypeTerm => {
        if (a.k === "declaration") return reference(a.declaration, []);
        if (a.k === "generic") {
          const parts = a.declarations.map(g => reference(g, [tagTerm(a.values)]));
          const [only] = parts;
          return only && parts.length === 1 ? only : { k: "intersection", parts, span };
        }
        const made = synthetic(a.name);
        if (made.fresh) {
          const fields: Field[] = [{ name: table.description.tag.field, optional: false, readonly: true, type: tagTerm(a.values), span }];
          const stable: string[] = table.tagStable(a.values) ? [table.description.tag.field] : [];
          const methods: FlatMember[] = [];
          // Every method's definition, in member order, whether or not the
          // residual shares it.
          const written: FlatMember[] = [];
          for (const s of a.fields) {
            const [first] = s.sources;
            // A method some replaced shape states optional is forgotten: the
            // residual relates to the shapes stating it required and to those
            // stating it optional alike.
            if (first && isMethod(first.member) && (s.optional || !shared(first.member, []))) {
              written.push(...s.sources.map(x => x.member));
              continue;
            }
            if (first && shared(first.member, []) &&
                s.sources.every(x => x.member.owner === first.member.owner)) {
              methods.push(first.member);
              written.push(first.member);
              continue;
            }
            const read = s.sources.map(x => readMember(x.member, [x.value], x.value));
            const types: TypeTerm[] = [];
            for (const r of read) if (!types.some(t => unspanned(t) === unspanned(r.type))) types.push(r.type);
            const [one] = types;
            if (!one) continue;
            fields.push({ name: s.name, readonly: true, optional: s.optional || read.some(r => r.optional),
              type: types.length === 1 ? one : { k: "union", parts: types, span }, span });
            if (s.sources.every(x => table.stable(x.member))) stable.push(s.name);
          }
          written.forEach(methodBase);
          definitions.push({ declaration: made.id, parameters: [], bases: methodOwners(methods), expression: shape(fields, stable) });
        }
        return made.term;
      };
      const tag = table.tagOf(node);
      if (tag.k === "open") {
        const arms = table.arms(node, selection);
        const union = (selected: readonly FamilyArm[]): TypeTerm => {
          const parts = selected.map(arm);
          const [only] = parts;
          return only && parts.length === 1 ? only : parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
        };
        definitions.push({ declaration: identity, parameters, bases: [], expression: union(arms) });
        // A listed node guard's promise, at the family's root: the arms
        // whose tags meet the guard's set (HOST-FAMILIES.md, "Guards as
        // values").
        if (node.name.text === table.description.root.name)
          for (const [name, values] of context.guardPromises.get(marker) ?? []) {
            const made = synthetic(name);
            if (!made.fresh) continue;
            const armValues = (a: FamilyArm): readonly TagValue[] =>
              a.k === "declaration" ? table.tagsOf(a.declaration) : a.values;
            definitions.push({ declaration: made.id, parameters: [], bases: [],
              expression: union(arms.filter(a => armValues(a).some(v => values.includes(v)))) });
          }
      } else {
        // Optional where it is at any tag the declaration's values can have:
        // a generic declaration's every application, a literal set's every tag.
        const tags = table.tagsOf(node);
        const flat = table.flatten(node);
        // Every method's definition is written, whether or not this reading
        // shares it, so readings that differ only by corrections number their
        // definitions alike.
        flat.filter(isMethod).forEach(methodBase);
        definitions.push({ declaration: identity, parameters, bases: methodOwners(flat.filter(f => shared(f, tags))),
          expression: shape(flat.filter(f => !shared(f, tags)).map(f => readMember(f, tags, null)),
            flat.filter(f => !shared(f, tags) && !isMethod(f) && table.stable(f)).map(f => f.name)) });
      }
      continue;
    }
    let expression = ts.isTypeAliasDeclaration(node)
      ? typeTerm(scope, node.type)
      : ts.isClassDeclaration(node)
        ? mergedClass(classInstance(scope, node, [node.getStart(source), node.end], admitted), parts.flatMap(part => {
            if (part === node || !ts.isInterfaceDeclaration(part)) return [];
            const file = part.getSourceFile();
            return [members(scopeOf(file), part.members.filter(admitted), part, [part.getStart(file), part.end], true)];
          }), (at, message) => scope.fail(at, message), node)
        : mergeMembers(parts.map(part => {
            const file = part.getSourceFile();
            if (!ts.isInterfaceDeclaration(part)) return scope.fail(part, "a declaration merged with an interface is not one");
            return members(partScope(part), part.members.filter(admitted), part,
              [part.getStart(file), part.end], true);
          }), (at, message) => scope.fail(at, message), node);
    // A host type's members are readonly views, whether or not they are
    // declared `readonly` (COMPILER-API.md, reading rule 1): a client write
    // to one is refused, and a test of one narrows as an invariant field's.
    // A member whose reads give no one value for a node's life is no member
    // of the host type's shape (the active family description's `omitted`,
    // declared as reviewed): every read of it, in any form, is a read of a
    // member the type does not state, and no structural type requiring it
    // admits a value of the host type.
    if (context.hostType(node) && expression.k === "object") {
      const omitted = ts.isInterfaceDeclaration(node)
        ? (familyOfFile(node.getSourceFile().fileName)?.omitted ?? []).filter(m => m.owner === node.name.text).map(m => ({ name: m.member, text: m.text })) : [];
      for (const entry of omitted) {
        const declared = parts.flatMap(part => ts.isInterfaceDeclaration(part) ? part.members : [])
          .filter(m => { const name = nameOf(m); return !!name && ts.isIdentifier(name) && name.text === entry.name; });
        if (declared.length !== 1 || declared.some(m => m.getText(m.getSourceFile()).trim() !== entry.text))
          throw Error(`${node.name?.text}.${entry.name} is not declared as reviewed: ${entry.text}`);
      }
      // A member declared `any` states nothing (reading rule 2): an optional
      // member of type `unknown`, as the brands (`_expressionBrand: any`),
      // which no runtime node owns, are read.
      const anyMembers = new Set(parts.flatMap(part => ts.isInterfaceDeclaration(part) || ts.isClassDeclaration(part)
        ? [...part.members] : []).flatMap(m => {
          const name = nameOf(m);
          return name && ts.isIdentifier(name) && readsAsOptionalUnknown(m) ? [name.text] : [];
        }));
      // The host produces each member: a branded string there is read as a
      // string, and one the client would produce refused (reading rule 5).
      // A view's methods are the sync API's requests, read at their
      // statement (T6, `requestReading`).
      const request = (f: { name: PropertyKey }): boolean =>
        !!named && named.members.some(m => m.name === f.name && isRequest(named.owner, m));
      expression = { ...expression, fields: expression.fields
        .filter(f => !omitted.some(m => m.name === f.name))
        .map(f => ({ ...f, readonly: true, optional: f.optional || (typeof f.name === "string" && anyMembers.has(f.name)),
          type: hostBrands(request(f) ? requestReading(f.type) : f.type, true, context.isBrand,
            message => { throw Error(`${message} in ${identity.module}#${identity.name}.${String(f.name)}`); }) })) };
    }
    // Native promise observation uses PromiseResolve's constructor equality
    // fast path. Its standard constructor and methods are inherited, and a
    // promise owns none of those keys. The ordinary prototype/own-key
    // contracts preserve this requirement through structural writable aliases.
    if (parts.some(part => ts.isInterfaceDeclaration(part) && part.name.text === "Promise" &&
        context.libraryFile(part.getSourceFile()))) {
      if (parts.some(part => !context.libraryFile(part.getSourceFile())))
        scope.fail(node, "a source augmentation of native Promise is outside the fragment: native factories must meet the built-in reviewed Promise contract");
      if (expression.k !== "object" || expression.prototype || expression.stringIndex ||
          expression.numberIndex || expression.symbolIndex || expression.calls.length)
        throw Error("the native Promise declaration must be an ordinary interface");
      const span = expression.span;
      const payload: TypeTerm = { k: "binder", name: "NativePayload", span };
      const promiseAt = (arg: TypeTerm): TypeTerm => ({ k: "reference", args: [arg], span,
        reference: { name: "Promise", span, arguments: [span], target: identity } });
      // catch and finally forward a fulfilled input by resolving a fresh
      // promise. The receiver's payload must therefore stay non-thenable.
      // The payload binder belongs to the callable, preserving covariance of
      // Promise itself and requiring the bound at every actual receiver.
      // `then` and `catch` resolve their callbacks' results: a native
      // promise is adopted through its standard `then`, and any other value
      // fulfills the result. A `PromiseLike` there is read as the native
      // promise, which a source thenable is not; elsewhere it stays the
      // structural record it is declared.
      const assimilated = (type: TypeTerm): TypeTerm =>
        type.k === "union" ? { ...type, parts: type.parts.map(assimilated) }
        : type.k === "reference" && type.reference.name === "PromiseLike" &&
            /typescript\/lib\//.test(type.reference.target.module) && type.args.length === 1 && type.args[0]
          ? promiseAt(type.args[0]) : type;
      const callbackResults = (type: TypeTerm): TypeTerm =>
        type.k === "union" ? { ...type, parts: type.parts.map(callbackResults) }
        : type.k === "function" ? { ...type, result: assimilated(type.result) } : type;
      const resolving = (type: TypeTerm): TypeTerm =>
        type.k === "scheme" ? { ...type, signatures: type.signatures.map(signature => signature.k === "function"
          ? { ...signature, params: signature.params.map(callbackResults) } : signature) }
        : type.k === "function" ? { ...type, params: type.params.map(callbackResults) } : type;
      const nativeFields = expression.fields.map(declared => {
        const field = declared.name === "then" || declared.name === "catch"
          ? { ...declared, type: resolving(declared.type) } : declared;
        if (field.name !== "catch" && field.name !== "finally") return field;
        const type = field.type;
        const binders = type.k === "scheme" ? type.binders : [];
        const signatures = (type.k === "scheme" ? type.signatures : type.k === "function" ? [type] : [])
          .filter((signature): signature is Extract<TypeTerm, { k: "function" }> => signature.k === "function");
        if (!signatures.length || parameters.length !== 1)
          throw Error(`the native Promise.${field.name} declaration has an unsupported signature`);
        const receiver = promiseAt(payload);
        // finally assimilates the cleanup result even though its public
        // declaration discards that result. Native cleanup promises use the
        // constructor fast path; other results must be stably non-thenable.
        const amended = signatures.map(signature => {
          let callbacks = 0;
          const cleanup = (type: TypeTerm): TypeTerm => {
            if (type.k === "union") return { ...type, parts: type.parts.map(cleanup) };
            if (type.k === "atom" && (type.name === "undefined" || type.name === "null")) return type;
            if (type.k !== "function" || type.params.length || type.rest ||
                type.receiver || type.result.k !== "atom" || type.result.name !== "void")
              throw Error("the native Promise.finally cleanup parameter has an unsupported signature");
            callbacks++;
            return { ...type, result: { k: "union", span,
              parts: [nonThenable, promiseAt({ k: "atom", name: "unknown", span })] } };
          };
          const params = field.name === "finally" ? signature.params.map(cleanup) : signature.params;
          if (field.name === "finally" && (params.length !== 1 || callbacks !== 1))
            throw Error("the native Promise.finally declaration must take one optional cleanup callback");
          return { ...signature, receiver, params, result: substitute(signature.result, [payload]) };
        });
        const updated: TypeTerm = { k: "scheme", span: type.span,
          binders: [...binders, { name: "NativePayload", bound: null, resolution: null, default: null, span }],
          signatures: amended };
        return { ...field, readonly: true, type: updated };
      });
      // Method members already describe lookup along the receiver's prototype
      // chain. Keep their host-relative contracts on the receiver; the
      // prototype slots state presence and prohibit own replacements.
      const isMethod = (type: TypeTerm): boolean =>
        (type.k === "scheme" && type.signatures.every(signature =>
          signature.k === "function" && signature.receiver?.k === "self")) ||
        (type.k === "function" && type.receiver?.k === "self") ||
        (type.k === "intersection" && type.parts.every(isMethod));
      const methods = nativeFields.filter(field => isMethod(field.type));
      expression = { ...expression, fields: methods,
        prototype: { ...expression, fields: [...nativeFields.map(field =>
          isMethod(field.type) ? { ...field, readonly: true,
            type: { k: "atom" as const, name: "unknown" as const, span } } : field),
          { name: "constructor", optional: false, readonly: true,
            type: { k: "atom", name: "unknown", span }, span }] } };
    }
    // A class's `implements` clauses are obligations on the class, not part of
    // its instance type; the class it extends is a base of that type, as an
    // interface's are.
    const bases = view ? [] : parts.flatMap(part => {
      if (!ts.isInterfaceDeclaration(part) && !ts.isClassDeclaration(part)) return [];
      const file = part.getSourceFile();
      const read = (t: TypeNode): TypeTerm => typeTerm(partScope(part), t);
      return (part.heritageClauses ?? []).filter(clause =>
          !(ts.isClassDeclaration(part) && clause.token === ts.SyntaxKind.ImplementsKeyword)).flatMap(clause => {
          if (clause.token !== ts.SyntaxKind.ExtendsKeyword)
            throw Error(`unsupported heritage in ${identity.module}#${identity.name}`);
          return clause.types.map(base => {
            if (!ts.isIdentifier(base.expression))
              throw Error(`qualified heritage in ${identity.module}#${identity.name}`);
            // A class extending the standard `Error` is, beside its own
            // members, what `Error` constructs (SOURCE-ELABORATION.md, a
            // class extending `Error`).
            if (ts.isClassDeclaration(part) && base.expression.text === "Error" && !base.typeArguments?.length &&
                context.libraryFile(lookup(base.expression, `${identity.module}#Error`).getSourceFile()))
              return errorInstance([base.getStart(file), base.end]);
            return reference(file, base.expression, base.typeArguments ?? [],
              [base.getStart(file), base.end], read, true);
          });
        });
    });
    definitions.push({ declaration: identity, parameters, bases, expression });
    // A record written as one: an interface or an alias read as its declared
    // body, outside a class, a host type and a view; or an alias of a named
    // type, whose shape is that type's.
    if (!view && !context.hostType(node) && !parts.some(ts.isClassDeclaration) &&
        ((expression.k === "object" && !expression.prototype && !expression.host) ||
          (ts.isTypeAliasDeclaration(node) && expression.k === "reference")))
      context.record(identity);
    } catch (error) {
      passToolFailure(error);
      if (!context.diagnostic) throw error;
      context.diagnostic(identity, messageOf(error));
      // Generated definitions and their availability marks form one transaction.
      // Queue entries and symbols keep their stable identities; a later user of
      // a rolled-back synthetic definition regenerates it at that identity.
      definitions.splice(before);
      if (availableBefore) {
        seen.clear();
        for (const key of availableBefore) seen.add(key);
      }
      const parameters = applied ? [] : context.parameters(node).map((p): TypeDefinition["parameters"][number] => ({
        name: p.name.text, span: [p.name.getStart(p.name.getSourceFile()), p.name.end],
        defaulted: !!p.default }));
      definitions.push({ declaration: identity, parameters, bases: [],
        expression: { k: "atom", name: "unknown", span: identity.span } });
    }
  }
}
