/** The declaration graph of one source file's types. TypeScript's checker,
 * under the file's configured project, decides which declaration every name
 * denotes: imports, reexports, package entries, `paths`, links and globals
 * resolve exactly as the compiler resolves them. This module turns each
 * declaration reached into a source equation, or refuses a form the fragment
 * cannot state; a refusal never drops a declaration. */
import { realpathSync } from "node:fs";
import { basename, dirname, join, relative, resolve, sep } from "node:path";
import { API, DiagnosticCategory, ElementFlags, SignatureKind, SymbolFlags, TypeFlags, isTupleType, isTypeReference, isUnionType, type Checker, type Program, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, ExportDeclaration, Identifier, ImportDeclaration, InterfaceDeclaration, Node, SourceFile, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";
// declaration-types.mts declares the declaration document this module writes, which the Fragment carries and Lean's EquationLowering reads.
// type-term.mts is the one reading of TypeScript type syntax as a source type term, which every declaration body here is read with.
// computed-types.mts states a type TypeScript computes (`typeof`, `keyof`, `T[K]`, template literals) as the equivalent source term, or refuses it.
// array-prototype.mts holds the reviewed contracts of the built-in prototypes, the only members of `Array.prototype` and the primitive prototypes this reader admits.
// intrinsics.mts declares the intrinsics this reader lists among the client's values: the trusted steps async functions, loops, spreads and patterns lower to.
// library-globals.mts is the reviewed overlay of the standard library's globals, the only global values this reader admits, at the signatures it states.
import type { Span } from "./span.mts";
import { nameOf } from "./syntax.mts";
import { classInstance, computedAlias, computedForm, expandMapped, mapped, members, oneTerm, optionalTerm, signature, signatures, substitute,
  typeTerm, validateAnnotation, type Mapped, type TermScope } from "./type-term.mts";
import { arrayPrototype, interfaceOverlay, overlay, primitiveKinds, primitivePrototype, primitivePrototypeName, type OverlayEntry,
  type OverlayLibrary, type PrimitiveKind } from "./array-prototype.mts";
import { intrinsics, intrinsicModule, resolutionIntrinsics, resolvableDeclaration, stableDefinition, iterateIteratorName, iterateRegExpStringName, iterateMapName, iterateSetName, iterateStringName,
  iterationIntrinsic, hasPropertyName, elementAtName, nonThenable, restFromIntrinsic, spreadName, enumIntrinsic, enumMembersTerm } from "./intrinsics.mts";
import { globalEntry, globalsOverlay, type GlobalEntry, type Stated } from "./library-globals.mts";
import { moduleEntries, reviewedText, type ModuleEntry } from "./library-modules.mts";
import { literalParts, regexpShape } from "./regexp-shape.mts";
import { dispatchIntrinsic, dispatchName, isDispatchMethod, libraryRegExpTerm, marks, nativeIterator, nativeIteratorDefinition,
  nativeRegExp, regexpIntrinsicName, reviewedRegExpMembers,
  type RegExpKeys } from "./regexp.mts";
import { computedType, enclosingBinders, inferredTerm, literalUnion, type ComputedContext } from "./computed-types.mts";
import type { DeclarationIdentity, DeclarationDocument, PropertyKey, Reference, TypeDefinition, TypeRoot, TypeTerm, ValueRoot } from "./declaration-types.mts";

type TypeDeclaration = TypeAliasDeclaration | InterfaceDeclaration | ClassDeclaration;
const isTypeDeclaration = (node: Node): node is TypeDeclaration =>
  ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node) || ts.isClassDeclaration(node);

/** A refusal located at a root of the client: an import declaration or one of
 * its own type declarations. */
export class DeclarationError extends Error {
  readonly at: Span;
  constructor(at: Span, message: string) {
    super(message);
    this.at = at;
  }
}

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
 * TypeScript, so a reference to it is read as that meaning (PROGRAM-TYPING.md,
 * "Library types"): `Array<T>` and `ReadonlyArray<T>` are the array types
 * `T[]` and `readonly T[]`, and a library type alias whose equation is a
 * mapped type, such as `Record<K, V>`, is that mapped type at the
 * reference's arguments. */
export type LibraryType =
  | { k: "array"; readonly: boolean }
  | { k: "mapped"; parameters: number; template: Mapped };

/** A reference to `library` at `args`, located at `span`. */
export function libraryTerm(library: LibraryType, args: readonly TypeTerm[], span: Span,
    fail: (message: string) => never): TypeTerm {
  if (library.k === "array") {
    const [element] = args;
    if (!element || args.length !== 1) return fail("an array type takes one type argument");
    return { k: "array", presence: "readable", readonly: library.readonly, element, span };
  }
  if (args.length !== library.parameters) return fail("a mapped library type needs all its type arguments");
  const t = library.template;
  return expandMapped({ ...t, key: substitute(t.key, args), value: substitute(t.value, args) }, span, fail);
}

type FunctionTerm = Extract<TypeTerm, { k: "function" }>;

/** The arguments of a reference to `library`: at a mapped type's key
 * parameter, the keys `keys` computes where it can (an alias of literals is
 * its literals), otherwise each argument as `read` reads it. */
export function libraryArguments(library: LibraryType, nodes: readonly TypeNode[], read: (node: TypeNode) => TypeTerm,
    keys?: (node: TypeNode) => TypeTerm | null): TypeTerm[] {
  const named: number[] = [];
  const mentions = (t: TypeTerm): void => {
    if (t.k === "parameter") named.push(t.index);
    else if (t.k === "union") t.parts.forEach(mentions);
  };
  if (library.k === "mapped") mentions(library.template.key);
  return nodes.map((node, i) => (named.includes(i) ? keys?.(node) : null) ?? read(node));
}

const isLibraryModule = (module: string): boolean => module.startsWith("typescript/lib/");

/** The configured project named on a command line: a tsconfig file, or the
 * directory holding one. */
export function tsconfigOf(path: string): string {
  const absolute = resolve(path);
  return absolute.endsWith(".json") ? absolute : join(absolute, "tsconfig.json");
}

/** Open `file` in its configured TypeScript project, which must be strict:
 * `tsconfigPath` when given, otherwise the project that owns the file. The
 * compiler reads the files on disk; nothing here overrides their text. */
function withProject<T>(file: string, tsconfigPath: string | undefined,
  use: (checker: Checker, client: SourceFile, root: string, program: Program) => T): T {
  const api = new API({ cwd: dirname(file) });
  try {
    const snapshot = api.updateSnapshot({ openFiles: [file],
      ...(tsconfigPath ? { openProjects: [tsconfigPath] } : {}) });
    const project = tsconfigPath
      ? snapshot.getProject(tsconfigPath)
      : snapshot.getDefaultProjectForFile(file);
    if (!project?.configFileName || !project.compilerOptions.strict)
      throw new DeclarationError([0, 0], `TypeScript did not load a strict tsconfig for ${file}`);
    const client = project.program.getSourceFile(file);
    if (!client) throw new DeclarationError([0, 0], `TypeScript did not load ${file}`);
    // The project itself must load: a type package it names, such as
    // `types: ["node"]`, that is not installed leaves its globals undeclared.
    const broken = project.program.getProgramDiagnostics().find(d => d.category === DiagnosticCategory.Error);
    if (broken) throw new DeclarationError([0, 0], `TypeScript reports an error in the project: ${broken.text}`);
    return use(project.checker, client, dirname(project.configFileName), project.program);
  } finally {
    api.close();
  }
}

/** A module's identity: the client by its absolute path, a standard library
 * file by name, anything else by its real path relative to the project. */
function moduleIds(clientFile: string, root: string): (file: SourceFile) => string {
  const client = realpathSync(clientFile);
  const projectRoot = realpathSync(root);
  return file => {
    const path = realpathSync(file.fileName);
    if (path === client) return clientFile;
    const inside = relative(projectRoot, path).split(sep).join("/");
    if (/^lib\..*\.d\.ts$/.test(basename(path)) && inside.startsWith("../"))
      return `typescript/lib/${basename(path)}`;
    return inside;
  };
}

/** What TypeScript binds `identifier` to, following import and export aliases. */
function targetOf(checker: Checker, identifier: Identifier) {
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
function expressionAt(file: SourceFile, span: Span): Node | null {
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
function importBindings(client: SourceFile): { local: Identifier; imported: string;
  specifier: string; span: Span; typeOnly: boolean }[] {
  return client.statements.filter(ts.isImportDeclaration).flatMap(node => {
    const span: Span = [node.getStart(client), node.end];
    const clause = node.importClause;
    if (!clause || clause.name || !clause.namedBindings || !ts.isNamedImports(clause.namedBindings) ||
        !ts.isStringLiteral(node.moduleSpecifier))
      throw new DeclarationError(span, "only named imports are resolved");
    const specifier = node.moduleSpecifier.text;
    // The unstable AST exposes this runtime field but omits it from the
    // ImportClause interface.
    const clauseTypeOnly = "isTypeOnly" in clause && clause.isTypeOnly === true;
    return clause.namedBindings.elements.map(element => ({ local: element.name,
      imported: element.propertyName?.text ?? element.name.text, specifier, span,
      typeOnly: clauseTypeOnly || element.isTypeOnly }));
  });
}

/**
 * The declaration graph of `file`: one root per named import and per local
 * declaration at a span in `locals`, and every declaration reachable from them.
 * `client`, when given, is the parser's tree of the same file; TypeScript must
 * have read the same bytes, so the spans of both trees agree.
 */
export function collectDeclarations(file: string, options: {
  tsconfigPath?: string;
  client?: SourceFile;
  locals?: readonly Span[];
  /** The client's type-reference names that are neither imported nor its own
   * declarations: each that TypeScript binds to a global declaration becomes
   * a root. A type parameter is not one. */
  globals?: readonly Span[];
  /** Told each of the client's global type names, at its first reference
   * (`globals`), that TypeScript binds to a library type read at its meaning
   * rather than joining the graph (`LibraryType`). */
  library?: (span: Span, library: LibraryType) => void;
  /** The standard associated-result alias, resolved at a source name. */
  awaited?: (span: Span) => void;
  /** The verifier's resolution-qualification bound (`resolvable.d.ts`),
   * resolved at a source name. */
  resolvable?: (span: Span) => void;
  /** The verifier's observation-qualification bound (`resolvable.d.ts`),
   * resolved at a source name. */
  awaitable?: (span: Span) => void;
  /** A local alias whose complete body is expanded in the qualified scope. */
  associatedAlias?: (name: string, declaration: DeclarationIdentity) => void;
  /** The client uses arrays: `Array.prototype`'s contract joins the graph
   * (`array-prototype.mts`), at `arrays`, the first array the client writes. */
  arrays?: Span;
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
  /** The client's element reads `e[k]`: each whose object TypeScript types
   * as arrays and tuples only and whose key as `number`, no literal, is
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
  staticType?: (span: Span, result: TypeTerm | { refused: string }) => void;
  contextualParams?: readonly Span[];
  contextualParam?: (span: Span, result: TypeTerm | { refused: string }) => void;
  /** The client's calls `Object.assign(arrow, literal)` written without type
   * arguments: each is reported to `assignTypes` with the two TypeScript
   * infers, the arrow's function type and the literal's record, as the
   * callable form's annotations, or the reason no term states them. */
  assignCalls?: readonly Span[];
  assignTypes?: (span: Span, result: { functionType: TypeTerm; bagType: TypeTerm } | { refused: string }) => void;
  /** The client's top-level enum declarations: each must be one TypeScript
   * accepts, and each member, by its span, is reported to `enumMember` with
   * the value TypeScript computes for it, which is the value its emit writes
   * (PROGRAM-TYPING.md, "Enums"), or undefined where it computes none. */
  enums?: readonly Span[];
  enumMember?: (span: Span, value: string | number | undefined) => void;
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
  computedType?: (span: Span, result: TypeTerm | { refused: string }) => void;
  /** Type nodes of the client's annotations that may be a mapped type's keys:
   * each is reported to `keyType` with the union of literals and primitives
   * TypeScript computes for it, or null. */
  keyTypes?: readonly Span[];
  keyType?: (span: Span, keys: TypeTerm | null) => void;
  /** The computed keys `[k]` and `[S.k]` of the client's annotations' type
   * literals: each that names a `unique symbol` constant or readonly property
   * joins the symbols and is reported to `symbolName` with its index, any
   * other with the reason it names none. */
  symbolNames?: readonly Span[];
  symbolName?: (span: Span, result: number | { refused: string }) => void;
  /** Told each TypeScript error the gate reads while deciding whether a
   * declaration is clean, whether or not it refuses the source: every error
   * TypeScript reports in each file it examines, each once. */
  seen?: (diagnostic: SeenDiagnostic) => void;
} = {}): DeclarationDocument {
  const clientFile = resolve(file);
  return withProject(clientFile, options.tsconfigPath, (checker, client, root, program) => {
    if (options.client && options.client.getFullText() !== client.getFullText())
      throw new DeclarationError([0, 0], "TypeScript client source bytes differ");
    const idOf = moduleIds(clientFile, root);
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
    const identityOf = (node: TypeDeclaration): DeclarationIdentity => {
      const source = node.getSourceFile();
      // An anonymous class is refused where it is reached, so every
      // declaration here has a name.
      return { module: idOf(source), name: node.name?.text ?? "",
        span: [node.getStart(source), node.end] };
    };
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
      for (const statement of statementsOnPath(checker, identifier))
        clean(statement, `${idOf(statement.getSourceFile())} on the path to ${what}`);
      return nodes;
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
        only.name.text === "Awaited" && isLibraryModule(idOf(only.getSourceFile()));
    };
    const associatedAlias = (node: TypeAliasDeclaration, seen = new Set<TypeAliasDeclaration>()): boolean => {
      if (seen.has(node)) return false;
      seen.add(node);
      const visit = (part: Node): boolean => {
        if (ts.isTypeReferenceNode(part)) {
          if (awaited(part)) return true;
          const target = ts.isIdentifier(part.typeName) ? targetOf(checker, part.typeName)?.declarations[0]?.resolve() : undefined;
          if (target && ts.isTypeAliasDeclaration(target) && associatedAlias(target, seen)) return true;
        }
        return part.forEachChild(visit) ?? false;
      };
      return visit(node.type);
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
    const declarationOf = (nodes: readonly Node[], what: string): TypeDeclaration => {
      const declared = nodes.filter(isTypeDeclaration);
      const longest = Math.max(0, ...declared.map(n => n.typeParameters?.length ?? 0));
      const node = declared.find(n => (n.typeParameters?.length ?? 0) === longest);
      const types = node ? [node, ...declared.filter(n => n !== node)] : declared;
      if (!node || nodes.some(n => !isTypeDeclaration(n) && !ts.isVariableDeclaration(n) &&
            !ts.isFunctionDeclaration(n)) ||
          (types.length > 1 && !types.every(ts.isInterfaceDeclaration)))
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
      } catch {
        return null;
      }
    };
    // A standard library type read at its meaning (`LibraryType`). Every
    // declaration TypeScript binds the name to must be the library's, so a
    // client that declares its own `Array`, merging into the global one, is
    // read as any other interface.
    const library = (identifier: Identifier, what: string): LibraryType | null => {
      const nodes = (targetOf(checker, identifier)?.declarations ?? []).map(d => d.resolve());
      const types: TypeDeclaration[] = [];
      for (const node of nodes) {
        if (!node || !isLibraryModule(idOf(node.getSourceFile()))) return null;
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
        parts.every(part => isLibraryModule(idOf(part.getSourceFile())));
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
      const type = checker.getTypeFromTypeNode(node);
      return type ? literalUnion(type, [node.getStart(node.getSourceFile()), node.end]) : null;
    };
    // Whether a name denotes a standard library value, such as `Symbol`.
    const isLibraryValue = (name: Identifier): boolean => {
      const nodes = (targetOf(checker, name)?.declarations ?? []).map(d => d.resolve());
      return nodes.length > 0 && nodes.every(n => !!n && isLibraryModule(idOf(n.getSourceFile())));
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
    const valueScope = (node: Node, what: string, binders: string[] = []): TermScope => {
      const source = node.getSourceFile();
      return {
        source,
        annotation: false,
        awaited,
        associatedAlias: part => {
          const target = ts.isIdentifier(part.typeName) ? targetOf(checker, part.typeName)?.declarations[0]?.resolve() : undefined;
          return target && ts.isTypeAliasDeclaration(target) && associatedAlias(target) ? target : null;
        },
        // An alias's body, its parameters read as the reference's arguments.
        equation: (reference) => {
          const alias = reference.reference.target && aliasNodes.get(aliasKey(reference.reference.target));
          const parameters = (alias?.typeParameters ?? []).map(p => p.name.text);
          if (!alias || reference.args.length !== parameters.length) return null;
          let body = alias.type;
          while (ts.isParenthesizedTypeNode(body)) body = body.type;
          if (!(ts.isArrayTypeNode(body) || ts.isTupleTypeNode(body) || ts.isTypeReferenceNode(body) ||
              (ts.isTypeOperatorNode(body) && body.operator === ts.SyntaxKind.ReadonlyKeyword)))
            return null;
          const outer = valueScope(alias, what);
          return typeTerm({ ...outer, named: (part, pos, read) => {
            const index = ts.isIdentifier(part.typeName) ? parameters.indexOf(part.typeName.text) : -1;
            const argument = reference.args[index];
            if (index < 0 || !argument) return outer.named(part, pos, read);
            if (part.typeArguments?.length) throw Error(`type parameter applied as constructor: ${part.typeName.getText(alias.getSourceFile())}`);
            return argument;
          } }, body, alias);
        },
        symbol: symbolOf,
        computed: (part, pos, read) => computedType(computedContext, part, pos, read),
        keys: keyTypeOf,
        fail: (_node, message) => { throw Error(`${message} in ${what}`); },
        named: (part, pos, read) => {
          const name = part.typeName;
          if (!ts.isIdentifier(name)) throw Error(`a qualified type reference in ${what}`);
          if (binders.includes(name.text)) {
            if (part.typeArguments?.length) throw Error(`type parameter applied as constructor: ${name.text}`);
            return { k: "binder", name: name.text, span: pos };
          }
          const known = library(name, `${idOf(source)}#${name.text}`);
          if (known) return libraryTerm(known, libraryArguments(known, part.typeArguments ?? [], read, keyTypeOf), pos,
            message => { throw Error(`${message} in ${what}`); });
          const targetNode = lookup(name, `${idOf(source)}#${name.text}`);
          // An alias TypeScript computes from its parameters is the type it
          // computes at this reference's arguments.
          if (computedAlias(targetNode, aliasOf)) return computedType(computedContext, part, pos, read);
          const parameters = mergedParameters(targetNode, partners);
          const args = part.typeArguments ?? [];
          if (args.length < parameters.filter(p => !p.default).length || args.length > parameters.length)
            throw Error(`type argument arity: ${identityOf(targetNode).module}#${name.text}`);
          valueStarts.push(targetNode);
          return { k: "reference", reference: { name: name.text, span: pos,
            arguments: args.map((arg): Span => [arg.getStart(source), arg.end]), target: identityOf(targetNode) },
            args: args.map(read), span: pos };
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
    const valueOf = (declared: readonly Node[], what: string): Omit<ValueRoot, "binding"> => {
      const nodes = declared.filter(n => !ts.isInterfaceDeclaration(n) && !ts.isTypeAliasDeclaration(n));
      const [node] = nodes;
      if (!node) throw Error(`unresolved value ${what}`);
      const source = node.getSourceFile();
      const span: Span = [node.getStart(source), node.end];
      if (nodes.length > 1) {
        const overloads = nodes.filter((n): n is ts.FunctionDeclaration => ts.isFunctionDeclaration(n) && !n.body);
        if (!overloads.length || !nodes.every(ts.isFunctionDeclaration) || nodes.length - overloads.length > 1)
          throw Error(`TypeScript found ${nodes.length} declarations for ${what}`);
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
        if (!ts.isVariableDeclarationList(list) || !(list.flags & ts.NodeFlags.Const) || !node.type)
          throw Error(`a declared value must be an annotated constant, function or class: ${what}`);
        clean(node, `${idOf(source)}#${node.name.text}`);
        // A `unique symbol` constant holds the symbol its declaration names,
        // the one `typeof` it denotes (`symbolOf`): its value is that
        // singleton. One whose symbol is not known (made otherwise) is a
        // symbol.
        const type = node.type;
        const unique = ts.isTypeOperatorNode(type) && type.operator === ts.SyntaxKind.UniqueKeyword &&
          type.type.kind === ts.SyntaxKind.SymbolKeyword;
        const symbol = unique ? (() => { try { return symbolOf(node.name); } catch { return null; } })() : null;
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
        return { declaration: identity, construct: true, typeParams, type: { k: "constructor", params, rest: null,
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
      const overloads = declared.filter((n): n is ts.FunctionDeclaration => ts.isFunctionDeclaration(n) && !n.body);
      if (!overloads.length || overloads.length !== declared.length ||
          overloads.some(o => !idOf(o.getSourceFile()).includes("@types/node/")))
        throw Error(`${what} is not a function Node's declarations declare, as the reviewed overlay of library modules states it`);
      const forms = entries.map(entry => {
        const match = overloads.find(o => reviewedText(o.getText(o.getSourceFile())) === entry.signature);
        if (!match) throw Error(`${what} is not declared as reviewed: ${entry.signature}`);
        const source = match.getSourceFile();
        const span: Span = [match.getStart(source), match.end];
        const term: Extract<TypeTerm, { k: "function" }> = { k: "function", effect: "unrestricted", receiver: null,
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
      applied: (alias, args) => {
        const what = `${idOf(alias.getSourceFile())}#${alias.name.text}`;
        const parameters = (alias.typeParameters ?? []).map(p => p.name.text);
        const outer = valueScope(alias, what);
        const scope: TermScope = { ...outer, named: (part, pos, read) => {
          const index = ts.isIdentifier(part.typeName) ? parameters.indexOf(part.typeName.text) : -1;
          const argument = args[index];
          if (index < 0 || !argument) return outer.named(part, pos, read);
          if (part.typeArguments?.length) throw Error(`type parameter applied as constructor: ${part.typeName.getText(alias.getSourceFile())}`);
          return argument;
        } };
        return node => typeTerm(scope, node, alias);
      },
      equation: reference => valueScope(client, "an alias's equation").equation?.(reference) ?? null,
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
    for (const binding of importBindings(client)) {
      try {
        // A function with overloads is its several declarations; any other
        // name must have one.
        const nodes = resolveDeclarations(binding.local, binding.local.text);
        const reviewed = moduleEntries(binding.specifier, binding.imported);
        if (!binding.typeOnly && reviewed.length) {
          values.push({ binding: { local: binding.local.text, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...moduleValue(nodes, reviewed, binding.local.text) });
          continue;
        }
        const [node] = nodes;
        if (!node || (nodes.length > 1 && !nodes.every(ts.isFunctionDeclaration)))
          throw Error(`TypeScript found ${nodes.length} declarations for ${binding.local.text}`);
        // A class is a type and, imported as a value, a constructor too.
        if (!binding.typeOnly && !(ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)))
          values.push({ binding: { local: binding.local.text, imported: binding.imported,
            specifier: binding.specifier, span: binding.span }, ...valueOf(nodes, binding.local.text) });
        if (!isTypeDeclaration(node)) continue;
        const declaration = lookup(binding.local, binding.local.text);
        roots.push({ node: declaration, root: { binding: { kind: "import", local: binding.local.text,
          imported: binding.imported, specifier: binding.specifier, span: binding.span },
        declaration: identityOf(declaration) } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        throw new DeclarationError(binding.span, error instanceof Error ? error.message : String(error));
      }
    }
    // The client's ambient declarations (PROGRAM-TYPING.md,
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
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
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
        if (roots.some(r => r.node === node) || computedAlias(node, aliasOf)) continue;
        roots.push({ node, root: { binding: { kind: "local", local: declaration.name.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
            isLibraryModule(idOf(declaration.getSourceFile()))) {
          resolutionContextAt ??= span;
          options.awaited?.(span);
          continue;
        }
        if (ts.isTypeAliasDeclaration(declaration) && declaration.getSourceFile().fileName === resolvableDeclaration &&
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
        if (computedAlias(node, aliasOf)) continue;
        roots.push({ node, root: { binding: { kind: "global", local: identifier.text, span },
          declaration: identityOf(node) } });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
      if (!first || !parts.every(part => isLibraryModule(idOf(part.getSourceFile()))))
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
        args, span: [0, 0] };
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
            !isLibraryModule(idOf(property.getSourceFile())) ||
            property.getText(property.getSourceFile()).trim() !== `readonly ${name}: unique symbol;`)
          throw Error(`Symbol.${name} is not declared as reviewed`);
        return symbolOf(property.name);
      },
      reference: (node, args, span) => {
        valueStarts.push(node);
        const target = identityOf(node);
        return { k: "reference", reference: { name: target.name, span, arguments: args.map(() => span),
          target }, args, span };
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
    let arrayProto: TypeDefinition[] = [];
    if (options.arrays) {
      try {
        arrayProto = arrayPrototype(checker, client, overlayLibrary, options.arrayOverlay ?? overlay);
      } catch (error) {
        throw new DeclarationError(options.arrays, error instanceof Error ? error.message : String(error));
      }
    }
    // A primitive's members are read through its wrapper's prototype: its
    // contract joins the definitions, and the built-in prototype the values,
    // an assumption at that contract as an import is at its type.
    const primitiveProtos: TypeDefinition[] = [];
    const primitives = new Map<PrimitiveKind, Span>();
    for (const span of options.memberReceivers ?? []) {
      const receiver = expressionAt(client, span);
      if (!receiver) throw new DeclarationError(span, "TypeScript member receiver missing");
      const type = checker.getTypeAtLocation(receiver);
      for (const kind of type ? primitivesOf(type) : [])
        if (!primitives.has(kind)) primitives.set(kind, span);
    }
    for (const [kind, at] of primitives) {
      try {
        const definition = primitivePrototype(checker, client, overlayLibrary, kind);
        primitiveProtos.push(definition);
        const name = primitivePrototypeName(kind);
        values.push({ binding: { local: name, imported: name, specifier: prototypeSpecifier, span: at },
          declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: definition.declaration.name, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
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
        symbol.declarations.every(d => isLibraryModule(idOf(d.resolve()?.getSourceFile() ?? client)));
      if (named && library) return named;
      // A match array is an array (`regexp.mts` reads `RegExpExecArray` and
      // `RegExpMatchArray` as tuple views), which the host builds with
      // `ArrayCreate`: iterated as one.
      if (library && (symbol?.name === "RegExpExecArray" || symbol?.name === "RegExpMatchArray")) return "array";
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
      const type = checker.getTypeAtLocation(iterable);
      const kinds = [...new Set((type && isUnionType(type) ? type.getTypes() : type ? [type] : [])
        .map(iterationKind))];
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
            element => { nativeMatches(); return nativeIterator(element); });
          values.push({ binding: { local: intrinsic.name, imported: intrinsic.name,
            specifier: intrinsicModule, span },
            declaration: { module: intrinsicModule, name: intrinsic.name, span: [0, 0] },
            construct: false, typeParams: intrinsic.typeParams, type: intrinsic.type });
        } catch (error) {
          throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
      catch (error) { throw new DeclarationError(at, error instanceof Error ? error.message : String(error)); }
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
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
      }
    };
    if (options.intrinsics) listIntrinsics(options.intrinsics.span, options.intrinsics.names);
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
      if (objects.length && objects.every(t => checker.isArrayType(t) || checker.isTupleType(t)) &&
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
            // Evaluating a literal allocates the regex and runs no code.
            type: { k: "function", effect: "preservesInputHeap", receiver: null, params: [], rest: null,
              result: nativeRegExp(shape, nativeMatches()), span: [0, 0] } });
        } catch (error) {
          throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
          throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
        }
        intrinsicsListed.add(name);
      }
      options.dispatch?.(span, name);
    }
    for (const span of options.receiverTargets ?? []) {
      const name = identifierAt(client, span);
      const symbol = name && checker.getSymbolAtLocation(name);
      if (symbol && symbol.flags & SymbolFlags.Method) options.methodTarget?.(span);
    }
    // Global variables the client reads, such as Node's `process` (PROGRAM-TYPING.md,
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
        const selection = selectGlobal(checker, uses, { lookup, identityOf: idOf, clean, valueScope, partners,
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
        if ("construct" in selection) {
          values.push({ binding, construct: true, ...selection.construct });
          continue;
        }
        const definition = selection.definition;
        selections.push(definition);
        values.push({ binding, declaration: definition.declaration, construct: false, typeParams: [],
          type: { k: "reference", reference: { name: first.text, span: at, arguments: [],
            target: definition.declaration }, args: [], span: at } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        throw new DeclarationError(at, error instanceof Error ? error.message : String(error));
      }
    }
    // A private name reads the key of the member TypeScript binds it to.
    for (const span of options.privateNames ?? []) {
      const name = expressionAt(client, span);
      if (!name || !ts.isPrivateIdentifier(name)) throw new DeclarationError(span, "TypeScript private name missing");
      try {
        options.privateName?.(span, privateNameOf(name));
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
          throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
      if (!declaration || isLibraryModule(idOf(declaration.getSourceFile() ?? client))) continue;
      const key = declaration ? nameOf(declaration) : undefined;
      const target = key && ts.isComputedPropertyName(key) && ts.isPropertyAccessExpression(key.expression) &&
        ts.isIdentifier(key.expression.name) ? targetOf(checker, key.expression.name) : undefined;
      if (target?.declarations.some(d => isLibraryModule(idOf(d.resolve()?.getSourceFile() ?? client))))
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
    const readContextualTerm = (type: Type, span: Span): TypeTerm => {
      if (type.flags & TypeFlags.Any)
        throw Error("TypeScript types this unannotated closure parameter from its context as `any`, which states no contract");
      const literals = literalUnion(type, span);
      if (literals) return literals;
      const text = () => checker.typeToString(type);
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
      const symbol = type.getAliasSymbol() ?? type.getSymbol();
      const nodes = (symbol?.declarations ?? []).map(d => d.resolve());
      const [node] = nodes;
      if (nodes.length === 1 && node && isTypeDeclaration(node) && node.name && !isLibraryModule(idOf(node.getSourceFile()))) {
        const arguments_ = type.getAliasTypeArguments();
        const actuals = arguments_.length ? arguments_ : isTypeReference(type) ? checker.getTypeArguments(type) : [];
        const args = actuals.map(argument => contextualTerm(argument, span));
        if (args.length !== (node.typeParameters?.length ?? 0))
          throw Error(`the contextual type ${text()} does not state every declaration argument`);
        const declared = declarationOf([node], text());
        contextualStarts.push({ node: declared, span });
        return { k: "reference", reference: { name: node.name.text, span, arguments: args.map(() => span), target: identityOf(node) },
          args, span };
      }
      // A library regex type (`RegExpExecArray` for a match's callback), as
      // `regexp.mts` reads it.
      const library = nodes.filter((n): n is InterfaceDeclaration => !!n && ts.isInterfaceDeclaration(n));
      if (symbol && library.length && library.length === nodes.length &&
          library.every(n => isLibraryModule(idOf(n.getSourceFile())))) {
        const stated = libraryRegExp(symbol.name, library);
        if (stated) return stated;
      }
      throw Error(`TypeScript types this unannotated closure parameter from its context as ${text()}, which is ` +
        "not stated by primitives, literals, unions, intersections, arrays, tuples, type parameters and declarations by name");
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
        options.staticType?.(span, contextualTerm(type, span));
      } catch (error) {
        options.staticType?.(span, { refused: error instanceof Error ? error.message : String(error) });
      }
    }
    for (const span of options.contextualParams ?? []) {
      const parameter = parameterAt(span);
      if (!parameter) throw new DeclarationError(span, "TypeScript parameter missing");
      const type = checker.getTypeAtLocation(parameter.name);
      try {
        if (!type || type.isErrorType()) throw Error("TypeScript gives this unannotated closure parameter no type");
        options.contextualParam?.(span, contextualTerm(type, span));
      } catch (error) {
        options.contextualParam?.(span, { refused: error instanceof Error ? error.message : String(error) });
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
        options.assignTypes?.(span, { bagType, functionType: { k: "function", effect: "unrestricted", receiver: null,
          params, rest: null, result: contextualTerm(returned, span), span } });
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.assignTypes?.(span, { refused: "the type arguments TypeScript infers for this Object.assign: " +
          (error instanceof Error ? error.message : String(error)) });
      }
    }
    for (const span of options.enums ?? []) {
      const statement = client.statements.find(s => s.getStart(client) === span[0] && s.end === span[1]);
      if (!statement || !ts.isEnumDeclaration(statement))
        throw new DeclarationError(span, "TypeScript enum declaration missing");
      try {
        clean(statement, `enum ${statement.name.text}`);
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
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
          type: enumMembersTerm(members, at) });
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
      options.keyType?.(span, node ? keyTypeOf(node) : null);
    }
    for (const span of options.symbolNames ?? []) {
      const node = expressionAt(client, span);
      if (!node || !(ts.isIdentifier(node) || ts.isPropertyAccessExpression(node))) {
        options.symbolName?.(span, { refused: "a computed key names a symbol constant" });
        continue;
      }
      try {
        options.symbolName?.(span, symbolOf(node));
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.symbolName?.(span, { refused: error instanceof Error ? error.message : String(error) });
      }
    }
    // The client's computed types: each evaluated where it is written, with
    // the binders of the functions around it, or refused with the reason.
    for (const span of options.computed ?? []) {
      const node = computedAt(client, span);
      if (!node) throw new DeclarationError(span, "TypeScript computed type missing");
      // A global type's application is computed when the alias it names is.
      const alias = ts.isTypeReferenceNode(node) ? aliasOf(node) : null;
      if (ts.isTypeReferenceNode(node) && !(alias && computedAlias(alias, aliasOf))) continue;
      const what = `${idOf(client)}#${node.getText(client)}`;
      const scope = valueScope(node, what, enclosingBinders(node));
      try {
        options.computedType?.(span, computedType(computedContext, node, span, part => typeTerm(scope, part)));
      } catch (error) {
        if (error instanceof DeclarationError) throw error;
        options.computedType?.(span, { refused: error instanceof Error ? error.message : String(error) });
      }
    }
    const seen = new Set<string>();
    const definitions: TypeDefinition[] = [];
    const starts = [
      ...roots.map(({ root, node }) => ({ node, span: root.binding.span })),
      ...valueStarts.map((node, index): { node: TypeDeclaration; span: Span } =>
        ({ node, span: values[Math.min(index, values.length - 1)]?.binding.span ?? [0, 0] })),
      ...contextualStarts,
    ];
    for (const { node: start, span } of starts) {
      try {
        collect(start, seen, definitions, { lookup, identityOf, symbol: symbolOf, privateName: privateNameOf, partners, library, equation,
          libraryInterface, computed: (node, span, read) => computedType(computedContext, node, span, read),
          keys: keyTypeOf, alias: aliasOf, awaited });
      } catch (error) {
        throw new DeclarationError(span, error instanceof Error ? error.message : String(error));
      }
    }
    definitions.push(...selections, ...primitiveProtos, ...regexpDefinitions, ...(stableListed ? [stableDefinition] : []));
    // First, so its row follows the four fixed ones in every table.
    definitions.unshift(...arrayProto);
    // Trusted generic promise results have a stable non-thenable payload
    // contract, so fresh resolution preserves that payload. Bound each
    // type parameter a Promise or PromiseLike position names accordingly
    // (SOURCE-CONTRACTS.md, "Async functions and await"). An existing
    // fulfilled promise may retain an object that later acquires then.
    // The client's own bodies are checked at their source annotations.
    const clientModule = idOf(client);
    const trustedValues = values.map(v => v.binding.specifier === intrinsicModule ? v :
      { ...v, typeParams: promisedBinders(v.typeParams, v.type), type: promisedMethods(v.type) });
    const trustedDefinitions = definitions.map(d => d.declaration.module === clientModule ? d :
      { ...d, expression: promisedMethods(d.expression) });
    return { roots: roots.map(r => r.root), definitions: trustedDefinitions, values: trustedValues, symbols };
  });
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
        return;
      case "scheme": for (const f of t.signatures) visit(f, inside); return;
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
  if (type.k === "object")
    return { ...type, fields: type.fields.map(f => ({ ...f, type: promisedMethods(f.type) })),
      ...(type.prototype ? { prototype: promisedMethods(type.prototype) } : {}) };
  if (type.k === "scheme") return { ...type, binders: promisedBinders(type.binders, type) };
  if (type.k === "union" || type.k === "intersection") return { ...type, parts: type.parts.map(promisedMethods) };
  return type;
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
 * `uses` select (PROGRAM-TYPING.md, "Imported, ambient and global values"
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
/** A declaration's type parameters by position, as TypeScript merges an
 * interface's declarations: each position's parameter in the declaration
 * binding the longest list, and its bound and default with the declaration
 * stating them, in whose scope they are read. TypeScript requires the
 * declarations stating a position's bound, or its default, to agree. */
function mergedParameters(node: TypeDeclaration,
    partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>) {
  const parts = partners.get(node) ?? [node];
  return (node.typeParameters ?? []).map((parameter, index) => {
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

function selectGlobal(checker: Checker, uses: readonly Identifier[], context: SelectionContext):
    { definition: TypeDefinition } |
    { construct: { declaration: DeclarationIdentity; typeParams: ValueRoot["typeParams"]; type: TypeTerm } } |
    null {
  const [first] = uses;
  if (!first) throw Error("a global value without a reference");
  const name = first.text;
  const declarations = (checker.getSymbolAtLocation(first)?.declarations ?? []).map(d => d.resolve());
  const variables = declarations.filter((d): d is ts.VariableDeclaration =>
    !!d && ts.isVariableDeclaration(d) && !!d.type && ts.isIdentifier(d.name));
  const [declaration] = variables;
  if (!declaration || declarations.some(d => !d ||
      (!ts.isInterfaceDeclaration(d) && !typesOnly(d) && !variables.some(v => v === d))))
    throw Error(`the global ${name} is not an annotated variable`);
  const where = (node: Node, key: string) => `${context.identityOf(node.getSourceFile())}#${key}`;
  for (const variable of variables) context.clean(variable, where(variable, name));
  const spanOf = (node: Node): Span => [node.getStart(node.getSourceFile()), node.end];
  // A standard library global is read through the reviewed overlay: a
  // signature it does not list, with exactly the text reviewed, is refused.
  const library = variables.every(v => isLibraryModule(context.identityOf(v.getSourceFile())));
  const reviewed = (member: string | undefined, node: Node, what: string):
      (Omit<GlobalEntry, "stated"> & { stated?: Stated }) | undefined => {
    if (!library) return undefined;
    const text = node.getText(node.getSourceFile()).trim();
    const entry = globalEntry(context.overlay, name, member, text);
    if (!entry) throw Error(`${what} is not in the reviewed overlay of library globals: ${text}`);
    for (const definition of entry.definitions ?? []) context.define(definition);
    const stated = entry.stated;
    return { ...entry, stated: typeof stated === "function" ? stated(context.library) : stated };
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
      given);
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
      if (!entry?.test) throw Error(`${name} is not read as an instanceof test`);
      context.test(spanOf(parent), entry.test);
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
          const form: FunctionTerm = { k: "function", effect: "unrestricted", receiver: { k: "self", span: at }, params: stated.params,
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
      fields.push({ name: key, optional: false, readonly: scheme, span,
        type: selected.length === 1 && only ? only : { k: "intersection", parts: selected, span } });
    } else if (nodes.length === 1 && property && ts.isPropertySignatureDeclaration(property) && property.type &&
        !property.modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword)) {
      const entry = reviewed(key, property, what);
      context.clean(property, where(property, key));
      fields.push({ name: key, optional: property.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
        readonly: property.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
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
      if (library && !reviewed(undefined, signature, `${name} as a value`)?.value)
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
      calledConstructs.push({ binders: stated.binders, type: { k: "constructor", params: stated.params, rest: null,
        result: stated.result, span: spanOf(signature) } });
      return [];
    }
    // A call signature the overlay states instead of the declared one, as a
    // member's: its parameters bound the arguments.
    if (entry?.stated) {
      const stated = entry.stated;
      if (stated.binders.length) throw Error(`${what} is stated with binders, which a call signature cannot hold`);
      for (const call of calls) boundedArguments(call, stated, what);
      const at = spanOf(signature);
      return [{ k: "function", effect: "unrestricted", receiver: null, params: stated.params,
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
    const entry = reviewed(undefined, signature, whatNew);
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
    if (entry?.stated) {
      const stated = entry.stated;
      for (const expression of expressions)
        if ((expression.arguments?.length ?? 0) > stated.params.length ||
            expression.arguments?.some(ts.isSpreadElement))
          throw Error(`${whatNew} is read with at most ${stated.params.length} argument(s)`);
      return [{ binders: stated.binders,
        type: { k: "constructor", params: stated.params, rest: null, result: stated.result, span } satisfies TypeTerm }];
    }
    if (signature.typeParameters?.length) throw Error(`${whatNew} is generic`);
    context.clean(signature, where(signature, name));
    return signatures(scopeOf(signature, whatNew), signature.parameters, signature.type, signature, span, false)
      .map(form => {
        if (form.receiver) throw Error(`${whatNew} states its receiver`);
        const binders: string[] = [];
        return { binders,
          type: { k: "constructor", params: form.params, rest: form.rest, result: form.result, span } satisfies TypeTerm };
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
    if (distinct.some(f => f.binders.length)) throw Error(`${whatNew} selects several generic signatures`);
    const span = spanOf(first);
    return { construct: { declaration: identity, typeParams: [],
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
function collect(start: TypeDeclaration, seen: Set<string>, definitions: TypeDefinition[], context: {
  lookup: (identifier: Identifier, what: string) => TypeDeclaration;
  identityOf: (node: TypeDeclaration) => DeclarationIdentity;
  symbol: (written: Identifier | ts.PropertyAccessExpression) => number;
  privateName: (name: ts.PrivateIdentifier) => number;
  partners: ReadonlyMap<TypeDeclaration, readonly TypeDeclaration[]>;
  library: (identifier: Identifier, what: string) => LibraryType | null;
  /** A declaration's equation where it is not its declared body. */
  equation: (node: TypeDeclaration) => TypeTerm | null;
  /** The standard library interface of this name, such as `Iterator`. */
  libraryInterface: (name: string) => TypeDeclaration;
  /** A computed type's term (`computed-types.mts`). */
  computed: NonNullable<TermScope["computed"]>;
  /** The type alias a reference names, if any. */
  alias: (reference: ts.TypeReferenceNode) => TypeAliasDeclaration | null;
  awaited: NonNullable<TermScope["awaited"]>;
  /** A mapped type's keys as TypeScript computes them. */
  keys: NonNullable<TermScope["keys"]>;
}): void {
  const { lookup, identityOf, symbol, partners, library, equation } = context;
  const queue: TypeDeclaration[] = [start];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const node = queue[cursor];
    if (!node) throw Error("missing queued declaration");
    const identity = identityOf(node);
    const key = `${identity.module}#${identity.span[0]}:${identity.span[1]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const stated = equation(node);
    if (stated) {
      definitions.push({ declaration: identity, parameters: [], bases: [], expression: stated });
      continue;
    }
    const source = node.getSourceFile();
    const parameterNodes = node.typeParameters ?? [];
    const parameterNames = parameterNodes.map(parameter => parameter.name.text);
    if (new Set(parameterNames).size !== parameterNames.length)
      throw Error(`duplicate binder in ${identity.module}#${identity.name}`);
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
      // An alias TypeScript computes from its parameters is the type it
      // computes at this reference's arguments.
      if (written && computedAlias(targetNode, context.alias)) return computed(written, pos, read);
      const target = identityOf(targetNode);
      const targetParameters = mergedParameters(targetNode, partners);
      const required = targetParameters.filter(p => !p.default).length;
      if (arguments_.length < required || arguments_.length > targetParameters.length)
        throw Error(`type argument arity: ${target.module}#${target.name}`);
      const edge: Reference = { name: identifier.text, span: pos,
        arguments: arguments_.map(arg => [arg.getStart(source), arg.end]), target };
      queue.push(targetNode);
      return { k: "reference", reference: edge, args: arguments_.map(read), span: pos };
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
      const term = context.computed(part, pos, read);
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
      ...(body ? { body } : {}),
      symbol,
      privateName: context.privateName,
      keys: context.keys,
      computed,
      fail: (_node, message) => { throw Error(`${message} in ${identity.module}#${identity.name}`); },
      named: (part, pos, read) => {
        const name = part.typeName;
        if (!ts.isIdentifier(name)) throw Error(`a qualified type reference in ${identity.module}#${identity.name}`);
        const index = names.indexOf(name.text);
        if (index < 0) return reference(source, name, part.typeArguments ?? [], pos, read, false, part);
        if (part.typeArguments?.length)
          throw Error(`type parameter applied as constructor: ${name.text}`);
        return { k: "parameter", index, span: pos };
      },
    });
    const scope = scopeOf(source);
    const parts = partners.get(node) ?? [node];
    const partScope = (part: TypeDeclaration): TermScope =>
      scopeOf(part.getSourceFile(), (part.typeParameters ?? []).map(parameter => parameter.name.text));
    // A bound or default is read in the scope of the declaration stating it.
    const statedIn = (at: { part: TypeDeclaration; type: TypeNode | undefined }): TypeTerm | null =>
      at.type ? typeTerm(partScope(at.part), at.type) : null;
    let sawDefault = false;
    const parameters = mergedParameters(node, partners).map(merged => {
      const parameter = merged.parameter;
      if (sawDefault && !merged.default)
        throw Error(`required type parameter after default in ${identity.module}#${identity.name}`);
      sawDefault ||= !!merged.default;
      const parameterSpan: Span = [parameter.getStart(source), parameter.end];
      return { name: parameter.name.text, span: parameterSpan,
        bound: merged.bound ? statedIn({ part: merged.bound.part, type: merged.bound.at.constraint }) : null,
        default: merged.default ? statedIn({ part: merged.default.part, type: merged.default.at.defaultType }) : null };
    });
    // A standard library interface read through the overlay: only its listed
    // members, and no base.
    const overlaid = ts.isInterfaceDeclaration(node) && Object.hasOwn(interfaceOverlay, node.name.text) &&
        parts.every(part => isLibraryModule(identityOf(part).module))
      ? interfaceOverlay[node.name.text] : undefined;
    if (overlaid && ts.isInterfaceDeclaration(node)) {
      definitions.push({ declaration: identity, parameters, bases: [],
        expression: overlaidInterface(node, parts.filter(ts.isInterfaceDeclaration), overlaid, partScope,
          identityOf, symbol, (name, span) => {
          const target = context.libraryInterface(name);
          queue.push(target);
          return (args: TypeTerm[]): TypeTerm => ({ k: "reference", args, span,
            reference: { name, span, arguments: args.map(() => span), target: identityOf(target) } });
        }) });
      continue;
    }
    let expression = ts.isTypeAliasDeclaration(node)
      ? typeTerm(scope, node.type)
      : ts.isClassDeclaration(node)
        ? classInstance(scope, node, [node.getStart(source), node.end])
        : mergeMembers(parts.map(part => {
            const file = part.getSourceFile();
            if (!ts.isInterfaceDeclaration(part)) return scope.fail(part, "a declaration merged with an interface is not one");
            return members(partScope(part), part.members, part,
              [part.getStart(file), part.end], true);
          }), (at, message) => scope.fail(at, message), node);
    // Native promise observation uses PromiseResolve's constructor equality
    // fast path. Its standard constructor and methods are inherited, and a
    // promise owns none of those keys. The ordinary prototype/own-key
    // contracts preserve this requirement through structural writable aliases.
    if (parts.some(part => ts.isInterfaceDeclaration(part) && part.name.text === "Promise" &&
        isLibraryModule(identityOf(part).module))) {
      if (parts.some(part => !isLibraryModule(identityOf(part).module)))
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
      const nativeFields = expression.fields.map(field => {
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
    const bases = parts.flatMap(part => {
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
            return reference(file, base.expression, base.typeArguments ?? [],
              [base.getStart(file), base.end], read, true);
          });
        });
    });
    definitions.push({ declaration: identity, parameters, bases, expression });
  }
}
