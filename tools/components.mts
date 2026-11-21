/** The family of components a checked file's code lies in, and the
 * read-only frame's proposals about it (docs/drafts/readonly-handles.md):
 * the components and their interfaces, each code's innermost component, the
 * allocation sites with their marks and keys, the possible sites of values,
 * the crossings, the codes that escape, the client obligations and the
 * guarantee candidates. Everything here is a proposal: the checks of the
 * read-only frame read it, and decide nothing on its word.
 *
 * The family: the checked file's package, where the nearest `package.json`
 * above it states `exports`, its code every source file of the program in
 * the package's directory; else the file alone. Each such file is a module
 * component, nested in the package; each class body a class component,
 * nested in its innermost enclosing class or its module. A package's
 * interface is its manifest's `exports`, each target resolved to a source
 * identity (a `.ts` source, or a build output mapped back through the
 * `outDir` and `rootDir` of a configuration in the package's directory),
 * then the entry modules' exports, re-exports followed; it is unknown where
 * a subpath is a pattern or a target resolves to no source of the program.
 *
 * The flow is an inclusion analysis over the family's code, insensitive to
 * order and to field names: each binding, each code's parameters, receiver
 * and result, and each site's contents hold a set of possible sites and of
 * components a value may enter from outside (`incoming`). A component's
 * members are its entries and its codes that escape; their parameters and
 * receivers enter from outside. A call of code that may be outside a
 * component passes its arguments out and its result in; a call whose callee
 * is no code of the family is a native's, its result a site of its own that
 * may also be its receiver, an argument or their contents, and it may write
 * its arguments into its receiver. A read or a call TypeScript types
 * primitive, and a reference to a parameter declared primitive, holds no
 * reference. Marks are the least the crossings, the holds by bindings and
 * the stores allow, a site's mark for a component at least its mark for
 * each component enclosing it. Once the flow is solved, one more round
 * records what each set includes by the code's statements and the code's
 * events (stores, calls, throws, catches, held and exported bindings,
 * suspensions), which the verifier's checks of the read-only frame read
 * (`ComponentChecks`). */
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile, TypeNode } from "typescript/unstable/ast";
import { dirname, join, relative, resolve, sep } from "node:path";
import { listDirectory, orAbsent, present, readText, realPath } from "./files.mts";
import { clientsTags, representationTags } from "./bound-annotations.mts";
import type { CallEffect, Change, Frame, Region, Selector } from "./declaration-types.mts";
import { interfaceOverlay, overlay } from "./array-prototype.mts";
import { globalsOverlay } from "./library-globals.mts";
import { viewDefinitions } from "./library-types.mts";
import type { CallAst, ComponentAst, ComponentsAst, CrossingAst, EntryAst, FrameEntryAst, Mark, PlaceAst, PositionAst, ProtocolEntryAst, SiteAst, SourceAst, StoreAst, ValueAst,
  SuspensionAst, TypeShapeAst } from "./fragment.mts";
import type { Json } from "./calculus.mts";
import type { Span } from "./span.mts";

/** A program the family is read from: its files by absolute path, each
 * one's tree, and whether TypeScript's type of each node is primitive, so
 * that no value of it holds a reference. */
export type FamilyProgram = {
  files: readonly string[];
  sourceOf: (absolute: string) => SourceFile | null;
  primitive: (nodes: readonly Node[]) => boolean[];
  /** The method of an interface of the standard library each name of a
   * member access resolves to, with whether the interface is `Array` or
   * `ReadonlyArray` and the interface's name, or null. */
  libraryMembers: (nodes: readonly Node[]) => ({ name: string; array: boolean; owner: string } | null)[];
  /** Whether each node's type is an array or a tuple of primitives. */
  primitiveElements: (nodes: readonly Node[]) => boolean[];
};

/** **Which arguments a standard library method may call**, by its reviewed
 * overlay entry: each parameter's (`params`), the last applying to every
 * further argument where it is a rest parameter (`rest`). */
export type LibraryCalls = { params: readonly boolean[]; rest: boolean };

/** **The calls a reviewed overlay entry states** of the method `name` of the
 * standard library's interface `owner`: a prototype member of the arrays'
 * overlay, a collection's (`interfaceOverlay`), a typed array's reviewed
 * member (`viewDefinitions`), or a member of a global's constructor
 * interface (`globalsOverlay`). A parameter is called where the
 * reviewed declaration types it a function (its type states `=>`) or the
 * entry states that the host runs code on it (`admit`); a parameter of
 * another type, `any` among them, is not, no object being a proxy (DESIGN.md,
 * "Trust surface"). Null where no entry is reviewed. */
export function overlayCalls(owner: string, name: string): LibraryCalls | null {
  const fromSignature = (signature: string, admitted: string | null): LibraryCalls | null => {
    const open = signature.indexOf("(");
    if (open < 0) return null;
    let depth = 0;
    let close = -1;
    for (let i = open; i < signature.length; i++) {
      const ch = signature[i];
      if (ch === "(" || ch === "<" || ch === "[" || ch === "{") depth++;
      else if (ch === ")" || ch === ">" || ch === "]" || ch === "}") {
        if (ch === ">" && signature[i - 1] === "=") continue;
        depth--;
        if (depth === 0) { close = i; break; }
      }
    }
    if (close < 0) return null;
    const params: string[] = [];
    let cur = "";
    depth = 0;
    for (const ch of signature.slice(open + 1, close)) {
      if (ch === "," && depth === 0) { params.push(cur); cur = ""; continue; }
      if (ch === "(" || ch === "<" || ch === "[" || ch === "{") depth++;
      else if ((ch === ")" || ch === ">" || ch === "]" || ch === "}") && !cur.endsWith("=")) depth--;
      cur += ch;
    }
    if (cur.trim() !== "") params.push(cur);
    const called = params.map((p) => p.includes("=>") || (admitted !== null && p.trim().replace(/^\.\.\./, "").startsWith(`${admitted}`)));
    return { params: called, rest: params.length > 0 && (params[params.length - 1] ?? "").trim().startsWith("...") };
  };
  if (owner === "Array" || owner === "ReadonlyArray") {
    const e = overlay.find((x) => x.name === name);
    return e === undefined ? null : fromSignature(e.signature, null);
  }
  const collection = interfaceOverlay.get(owner)?.find((x) => x.name === name);
  if (collection !== undefined) return fromSignature(collection.signature, null);
  // A typed array's reviewed members (`library-types.mts`): a parameter of
  // function type is called.
  const view = viewDefinitions.find((d) => d.declaration.name === owner);
  if (view !== undefined) {
    const e = view.expression;
    const member = e !== null && e.k === "object" ? e.fields.find((x) => x.name === name) : undefined;
    const t = member?.type;
    return t !== undefined && t.k === "function"
      ? { params: t.params.map((q) => q.k === "function"), rest: t.rest !== null } : null;
  }
  if (owner.endsWith("Constructor")) {
    const g = globalsOverlay.find((x) => x.global === owner.slice(0, -"Constructor".length) && x.member === name);
    if (g !== undefined) return fromSignature(g.signature, g.admit?.parameter ?? null);
  }
  return null;
}

/** What the analysis is given: the checked file's path in its project (where
 * its package is found) and its tree; the checked file alone as a program,
 * and its project's program, opened where a package is found; the module
 * identity of a file as the declaration document gives it; a build
 * configuration; the guarantee candidates the lowering's reader elaborates;
 * and the gate's refusal at a node of the checked file. */
export type FamilyInput = {
  absolute: string;
  source: SourceFile;
  alone: FamilyProgram;
  project: () => FamilyProgram;
  locationOf: (absolute: string) => string;
  buildConfig: (path: string) => BuildConfig | null;
  guarantees: () => ComponentsAst["guarantees"];
  fail: (node: Node | null, message: string) => never;
};

/** **A member of the standard library's arrays with a fresh result**: its
 * reviewed overlay entry (`tools/array-prototype.mts`) states a fresh result
 * at its effect, or at every signature it states. */
export function freshArrayMember(name: string): boolean {
  const fresh = (e: CallEffect | undefined): boolean => e !== undefined && e.exits.normal.ensures.some((x) =>
    typeof x === "object" && "operation" in x && "freshSpine" in x.operation.post && x.operation.post.freshSpine.x === 0);
  return overlay.some((entry) => entry.name === name && (entry.from === "Array" || entry.from === "ReadonlyArray") &&
    (fresh(entry.effect) || (entry.stated !== undefined && entry.stated.length > 0 &&
      entry.stated.every((st) => fresh(st.effect ?? entry.effect)))));
}

/** **Whether no value of a type's shape holds storage**: a primitive, a union
 * of such shapes, or a named type whose definition is one
 * (`ComponentChecks.primitiveShape` states the same in Lean). */
export function shapePrimitive(t: TypeShapeAst | null, types: ComponentsAst["types"], visiting: ReadonlySet<number> = new Set()): boolean {
  if (t === null) return false;
  if (t === "primitive") return true;
  if (typeof t === "string") return false;
  if ("union" in t) return t.union.every((e) => shapePrimitive(e, types, visiting));
  if ("named" in t) {
    if (visiting.has(t.named)) return false;
    const row = types[t.named];
    return row !== undefined && shapePrimitive(row.definition, types, new Set([...visiting, t.named]));
  }
  return false;
}

/** **Whether a type's shape is read-only throughout** (the draft, "Read-only
 * types and crossings"): a primitive, `unknown` or a sealed handle; a
 * read-only array or tuple of such types; a record whose every member is a
 * `readonly` field of such a type; a union or an intersection of such types;
 * a named type whose definition is one, a recursive reference read as
 * writable. `ComponentChecks.readOnlyShape` states the same in Lean, which
 * derives each crossing's bit from it. */
export function shapeReadOnly(t: TypeShapeAst | null, types: ComponentsAst["types"], visiting: ReadonlySet<number> = new Set()): boolean {
  if (t === null) return false;
  if (t === "primitive" || t === "unknown" || t === "sealed") return true;
  if (t === "function" || t === "other") return false;
  if ("readonlyArray" in t) return shapeReadOnly(t.readonlyArray, types, visiting);
  if ("array" in t) return false;
  if ("tuple" in t) return t.tuple.readonly && t.tuple.elements.every((e) => shapeReadOnly(e, types, visiting));
  if ("record" in t) return t.record.every((m) => m.readonly && m.field && shapeReadOnly(m.type, types, visiting));
  if ("union" in t) return t.union.every((e) => shapeReadOnly(e, types, visiting));
  if ("intersection" in t) return t.intersection.every((e) => shapeReadOnly(e, types, visiting));
  if (visiting.has(t.named)) return false;
  const row = types[t.named];
  return row !== undefined && shapeReadOnly(row.definition, types, new Set([...visiting, t.named]));
}

/** The empty description: no component. */
export const noComponents: ComponentsAst = { components: [], codes: [], sites: [], values: [], crossings: [],
  stores: [], calls: [], throws: [], catches: [], holds: [], exports: [], thrown: null, suspensions: [], types: [],
  escapes: [], clients: [], guarantees: [], protocols: [], frameParts: [], frameEntries: [], frames: [] };

/** A build configuration: where it writes its outputs, the directory of
 * the sources they mirror, and the files it compiles. */
export type BuildConfig = { outDir: string | null; rootDir: string | null; fileNames: readonly string[] };
type Build = { outDir: string; rootDir: string; fileNames: readonly string[] };

type File = { absolute: string; location: string; source: SourceFile; module: number };
/** A set of the flow: a binding, a parameter or a call by its node, or a
 * code's result or receiver, a site's contents, a class's instances, or
 * the values thrown, by an object of its own. */
type Key = object;
type FlowRule = () => void;

/** A growing set stored by the solver. Transient sets have no copy cursor. */
class FlowTokens implements Iterable<number> {
  private readonly tokens: Set<number>;
  private added?: number[];
  private copies?: WeakMap<FlowTokens, number>;

  constructor(tokens: Iterable<number> = []) {
    this.tokens = new Set(tokens);
  }

  get size(): number { return this.tokens.size; }
  has(token: number): boolean { return this.tokens.has(token); }
  [Symbol.iterator](): SetIterator<number> { return this.tokens.values(); }

  add(token: number): void {
    const before = this.tokens.size;
    this.tokens.add(token);
    if (this.tokens.size > before) this.added?.push(token);
  }

  *since(start: number): Iterable<number> {
    if (start === this.size) return;
    const added = this.added ??= [...this.tokens];
    for (let i = start; i < added.length; i++) {
      const token = added[i];
      if (token !== undefined) yield token;
    }
  }

  copyFrom(source: FlowTokens): void {
    const copies = this.copies ??= new WeakMap();
    const start = copies.get(source) ?? 0;
    if (start === source.size) return;
    for (const token of source.since(start)) this.add(token);
    copies.set(source, source.size);
  }
}
type FlowValues = FlowTokens | Set<number>;

/** A rule reads dependencies as it runs, including those discovered through
 * new tokens. Only growth of a dependency schedules its readers. */
class FlowWorklist {
  private readonly readers = new Map<Key | string, Set<FlowRule>>();
  private pending = new Set<FlowRule>();
  private readonly grown = new Set<Key | string>();
  private deferred = new Set<FlowRule>();
  private runningDeferred = false;
  private current: FlowRule | null = null;

  get active(): boolean { return this.current !== null; }

  read(fact: Key | string): void {
    if (this.current === null) return;
    let readers = this.readers.get(fact);
    if (!readers) this.readers.set(fact, readers = new Set());
    readers.add(this.current);
  }

  grow(fact: Key | string): void {
    if (this.current !== null && this.readers.has(fact)) this.grown.add(fact);
  }

  add(rule: FlowRule): void {
    this.pending.add(rule);
  }

  /** A shared projection can establish its first value on demand. */
  run(rule: FlowRule): void {
    const parent = this.current;
    this.current = rule;
    try {
      rule();
    } finally {
      this.current = parent;
    }
  }

  /** An unresolved call is considered after its ordinary dependencies settle. */
  defer(): boolean {
    if (this.current === null || this.runningDeferred) return false;
    this.deferred.add(this.current);
    return true;
  }

  solve(beforeRule: () => void): void {
    while (this.pending.size > 0 || this.deferred.size > 0) {
      this.runningDeferred = this.pending.size === 0;
      const ready = this.runningDeferred ? this.deferred : this.pending;
      if (this.runningDeferred) this.deferred = new Set();
      else this.pending = new Set();
      for (const rule of ready) {
        beforeRule();
        this.run(rule);
      }
      for (const fact of this.grown)
        for (const rule of this.readers.get(fact) ?? []) this.pending.add(rule);
      this.grown.clear();
    }
    this.current = null;
    this.readers.clear();
  }
}
type Code = { node: Node; file: File; component: number; params: Node[]; result: Key; receiver: Key };
type Site = { node: Node; file: File; kind: SiteAst["kind"]; component: number };

const sourceExtension = /\.[cm]?tsx?$/;
const declarationFile = /\.d\.[cm]?ts$/;
const isSource = (path: string): boolean => sourceExtension.test(path) && !declarationFile.test(path) &&
  !path.split(sep).includes("node_modules");

/** The nearest `package.json` above `file`, below any `node_modules`, with
 * its parsed manifest. */
function manifestOf(file: string): { path: string; manifest: Json } | null {
  for (let at = dirname(file); ; at = dirname(at)) {
    if (at.split(sep).at(-1) === "node_modules") return null;
    const path = join(at, "package.json");
    const text = orAbsent(readText, path);
    if (text !== null) {
      try {
        const manifest: Json = JSON.parse(text);
        return { path, manifest };
      } catch {
        return null;
      }
    }
    if (dirname(at) === at) return null;
  }
}

const member = (j: Json | undefined, key: string): Json | undefined =>
  typeof j === "object" && j !== null && !Array.isArray(j) ? j[key] : undefined;

/** A subpath's string targets: a string, each string of an array, each
 * condition's targets; `null` excludes the subpath. */
function targetsOf(j: Json | undefined): string[] {
  if (typeof j === "string") return [j];
  if (Array.isArray(j)) return j.flatMap(targetsOf);
  if (typeof j === "object" && j !== null) return Object.values(j).flatMap(targetsOf);
  return [];
}

/** The source of a manifest's target: itself where it is a source of the
 * program; a build output mapped back through a configuration of the
 * package's directory (`outDir` to `rootDir`, `.js`, `.mjs`, `.cjs` and
 * declaration files to their sources); else a reason. A JSON target is data,
 * no code (`null`). */
function targetSource(root: string, target: string, sources: ReadonlySet<string>, configs: readonly Build[]):
    { source: string | null; build: Build | null } | { reason: string } {
  if (!target.startsWith("./")) return { reason: `the target ${target} is not relative to the package` };
  const absolute = resolve(root, target);
  if (/\.json$/.test(absolute)) return { source: null, build: null };
  if (sources.has(absolute)) return { source: absolute, build: null };
  const found = new Map<string, Build>();
  for (const build of configs) {
    const { outDir, rootDir } = build;
    const inside = relative(outDir, absolute);
    if (inside.startsWith("..") || inside === "") continue;
    const base = join(rootDir, inside).replace(/\.d\.([cm]?)ts$/, ".$1js");
    for (const candidate of [base.replace(/\.js$/, ".ts"), base.replace(/\.js$/, ".tsx"), base.replace(/\.mjs$/, ".mts"),
      base.replace(/\.cjs$/, ".cts")])
      if (candidate !== base && sources.has(candidate) && !found.has(candidate)) found.set(candidate, build);
  }
  const [only, ...others] = [...found];
  if (only !== undefined && others.length === 0) return { source: only[0], build: only[1] };
  return { reason: only === undefined ? `the target ${target} resolves to no source of the program`
    : `the target ${target} resolves to several sources` };
}

/** The entry modules a manifest's `exports` names, by subpath, and the
 * builds whose outputs they are; or the reason they are unknown. */
function exportsEntries(root: string, exports: Json, sources: ReadonlySet<string>,
    configs: readonly Build[]): { modules: string[]; builds: Build[] } | { reason: string } {
  const keys = typeof exports === "object" && exports !== null && !Array.isArray(exports) ? Object.keys(exports) : [];
  const subpaths: [string, Json | undefined][] = keys.length > 0 && keys.every((k) => k.startsWith("."))
    ? keys.map((k) => [k, member(exports, k)]) : [[".", exports]];
  const modules = new Set<string>();
  const builds = new Set<Build>();
  for (const [subpath, target] of subpaths) {
    if (subpath.includes("*")) return { reason: `the subpath pattern ${subpath}` };
    const targets = targetsOf(target);
    const resolved = new Set<string | null>();
    for (const t of targets) {
      const r = targetSource(root, t, sources, configs);
      if ("reason" in r) return { reason: `${subpath}: ${r.reason}` };
      resolved.add(r.source);
      if (r.build) builds.add(r.build);
    }
    const code = [...resolved].filter((s): s is string => s !== null);
    if (code.length > 1) return { reason: `${subpath}: its conditions name different sources` };
    if (code[0] !== undefined) modules.add(code[0]);
  }
  return { modules: [...modules].sort(), builds: [...builds] };
}

/** The build configurations of a package's directory: each `tsconfig*.json`
 * there stating both `outDir` and `rootDir`. */
function buildConfigs(root: string, read: FamilyInput["buildConfig"]): Build[] {
  const entries = orAbsent(listDirectory, root) ?? [];
  return entries.filter((e) => /^tsconfig.*\.json$/.test(e.name)).flatMap((e) => {
    const c = read(join(root, e.name));
    return c && c.outDir !== null && c.rootDir !== null
      ? [{ outDir: c.outDir, rootDir: c.rootDir, fileNames: c.fileNames.map((n) => resolve(root, n)) }] : [];
  });
}

const leading = (file: SourceFile, node: Node): string => file.text.slice(node.pos, node.getStart(file));
const exported = (node: Node): boolean => {
  const modifiers = ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node) || ts.isVariableStatement(node) ||
    ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node) || ts.isEnumDeclaration(node) ? node.modifiers : undefined;
  return !!modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
};
const defaulted = (node: Node): boolean => {
  const modifiers = ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node) ? node.modifiers : undefined;
  return !!modifiers?.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword);
};
const unwrap = (e: Node): Node => {
  let x = e;
  while (ts.isParenthesizedExpression(x) || ts.isAsExpression(x) || ts.isSatisfiesExpression(x) || ts.isNonNullExpression(x))
    x = x.expression;
  return x;
};
const functionLike = (n: Node): boolean => ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) ||
  ts.isMethodDeclaration(n) || ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n);
const classLike = (n: Node): boolean => ts.isClassDeclaration(n) || ts.isClassExpression(n);
const parametersOf = (n: Node): readonly Node[] =>
  ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
  ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n) ? n.parameters : [];
const bodyOf = (n: Node): Node | undefined =>
  ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
  ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n) ? n.body : undefined;
const nameText = (n: Node | undefined): string | null =>
  n === undefined ? null : ts.isIdentifier(n) || ts.isStringLiteral(n) || ts.isNumericLiteral(n) ? n.text : null;

/** A class member's name, where its kind has one. */
const memberName = (m: Node): Node | undefined =>
  ts.isMethodDeclaration(m) || ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m) || ts.isPropertyDeclaration(m)
    ? m.name : undefined;
const isStatic = (m: Node): boolean => {
  const modifiers = ts.isMethodDeclaration(m) || ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m) ||
    ts.isPropertyDeclaration(m) ? m.modifiers : undefined;
  return !!modifiers?.some((y) => y.kind === ts.SyntaxKind.StaticKeyword);
};
/** A method or an accessor a class's interface names: one no private name
 * names. */
const publicMethod = (m: Node): boolean => {
  const name = memberName(m);
  return functionLike(m) && !ts.isConstructorDeclaration(m) && !(name && ts.isPrivateIdentifier(name));
};

/** A member's name in its class's interface: `static`, `get` and `set`
 * before its key where it is one, `[computed]` for a computed key. */
const memberLabel = (m: Node): string =>
  `${isStatic(m) ? "static " : ""}${ts.isGetAccessorDeclaration(m) ? "get " : ts.isSetAccessorDeclaration(m) ? "set " : ""}${nameText(memberName(m)) ?? "[computed]"}`;

/** The identifiers a binding name binds. */
function boundNames(name: Node): Node[] {
  if (ts.isIdentifier(name)) return [name];
  if (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name))
    return name.elements.flatMap((e) => ts.isBindingElement(e) && e.name ? boundNames(e.name) : []);
  return [];
}

/** **The flow's tokens**: a site by its index, a component a value enters
 * from outside by `INCOMING` plus its index, at a writable position, or by
 * `INCOMING_RO` plus its index, reached read-only from a crossing in at a
 * read-only type. */
const INCOMING = 1 << 24;
const INCOMING_RO = 2 << 24;
/** The component of an incoming token. */
const componentOfToken = (t: number): number => t >= INCOMING_RO ? t - INCOMING_RO : t - INCOMING;
/** Whether an identifier is a reference to a binding: not a property's
 * name, a member's name or a declaration's own name. */
const reference = (n: Node): boolean => {
  const p = n.parent;
  if (!p) return false;
  if (ts.isPropertyAccessExpression(p) && p.name === n) return false;
  if ((ts.isPropertyAssignment(p) || ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p) || ts.isGetAccessorDeclaration(p) ||
      ts.isSetAccessorDeclaration(p) || ts.isPropertySignatureDeclaration(p) || ts.isMethodSignatureDeclaration(p)) && p.name === n)
    return false;
  if (ts.isBindingElement(p) && p.propertyName === n) return false;
  if ((ts.isVariableDeclaration(p) || ts.isParameterDeclaration(p) || ts.isFunctionDeclaration(p) || ts.isClassDeclaration(p) ||
      ts.isFunctionExpression(p) || ts.isClassExpression(p) || ts.isBindingElement(p)) && p.name === n) return false;
  return true;
};
const MARKS: readonly Mark[] = ["local", "internal", "exposed", "released"];
const rank = (m: Mark): number => MARKS.indexOf(m);

/** The family of components `input`'s file lies in, described. */
export function describeFamily(input: FamilyInput): ComponentsAst {
  const components: ComponentAst[] = [];
  const found = manifestOf(input.absolute);
  const exportsField = found === null ? undefined : member(found.manifest, "exports");
  const root = found === null || exportsField === undefined || exportsField === null ? null : dirname(found.path);
  // A package's code is read in the checked file's project.
  const program = root === null ? input.alone : input.project();
  const sources = new Set(program.files.filter(isSource).map((p) => resolve(p)));
  const realRoot = root === null ? null : realPath(root);
  const inDirectory = (p: string): boolean => realRoot !== null && !relative(realRoot, realPath(p)).startsWith("..");
  // The package's code: the files of the builds whose outputs its exports
  // name, where they name any; else every source of the program in its
  // directory. A file of the directory no such build compiles is outside it.
  const directory = [...sources].filter(inDirectory).sort();
  const entries = root === null || exportsField === undefined ? null
    : exportsEntries(root, exportsField, new Set(directory), buildConfigs(root, input.buildConfig));
  const built = entries !== null && "builds" in entries && entries.builds.length > 0
    ? new Set(entries.builds.flatMap((b) => b.fileNames)) : null;
  const code = built === null ? directory : directory.filter((p) => built.has(p));
  const packaged = entries !== null && code.includes(resolve(input.absolute));
  // The family's files: the package's code, else the file; read in the
  // program the package's code was found in.
  const paths = packaged ? code : [resolve(input.absolute)];
  const reading = packaged ? program : input.alone;
  let entryModules: string[] = [];
  if (packaged && found !== null && entries !== null) {
    if ("modules" in entries) entryModules = entries.modules;
    components.push({ kind: "package", location: input.locationOf(found.path), pos: null, parent: null,
      interface: "modules" in entries ? { known: { entries: [] } } : { unknown: { reason: entries.reason } } });
  }
  const packageIndex = components.length > 0 ? 0 : null;
  const files: File[] = [];
  for (const absolute of paths) {
    const source = absolute === resolve(input.absolute) && !packaged ? input.source : reading.sourceOf(absolute);
    if (source === null) continue;
    files.push({ absolute, location: input.locationOf(absolute), source, module: components.length });
    components.push({ kind: "module", location: input.locationOf(absolute), pos: null, parent: packageIndex,
      interface: { known: { entries: [] } } });
  }
  const fileOf = new Map(files.map((f) => [f.absolute, f]));
  const span = (f: File, n: Node): Span => [n.getStart(f.source), n.end];

  // Class components, each nested in the innermost class or module around it.
  const classComponent = new Map<Node, number>();
  const innermost = (n: Node, f: File): number => {
    for (let at: Node | undefined = n.parent; at; at = at.parent) {
      const c = classComponent.get(at);
      if (c !== undefined) return c;
    }
    return f.module;
  };
  for (const f of files) {
    const visit = (n: Node): void => {
      if (classLike(n)) {
        const parent = innermost(n, f);
        classComponent.set(n, components.length);
        components.push({ kind: "class", location: f.location, pos: span(f, n), parent, interface: { known: { entries: [] } } });
      }
      n.forEachChild(visit);
    };
    visit(f.source);
  }
  const ancestors = components.map((_, c): number[] => {
    const chain: number[] = [];
    for (let at: number | null = c; at !== null; at = components[at]?.parent ?? null) chain.push(at);
    return chain;
  });
  const enclosing = (c: number): readonly number[] => ancestors[c] ?? [];
  const within = (inner: number, outer: number): boolean => enclosing(inner).includes(outer);

  // Codes and sites.
  /** Where a set of the flow is stated: a node's own, or the code, site or
   * class it is of. */
  const anchors = new Map<Key, { node: Node; file: File }>();
  const codes: Code[] = [];
  const codeOf = new Map<Node, Code>();
  const worklist = new FlowWorklist();
  const sites: Site[] = [];
  let onSite: ((index: number, site: Site) => void) | undefined;
  const siteOf = new Map<Node, number>();
  const fileOfNode = new Map<Node, File>();
  const site = (node: Node, f: File, kind: SiteAst["kind"]): number => {
    const known = siteOf.get(node);
    if (known !== undefined) return known;
    const index = sites.length;
    const allocated = { node, file: f, kind, component: innermost(node, f) };
    sites.push(allocated);
    siteOf.set(node, index);
    onSite?.(index, allocated);
    return index;
  };
  for (const f of files) {
    fileOfNode.set(f.source, f);
    const visit = (n: Node): void => {
      if (functionLike(n)) {
        const code: Code = { node: n, file: f, component: innermost(n, f), params: [...parametersOf(n)], result: {}, receiver: {} };
        codes.push(code);
        codeOf.set(n, code);
        anchors.set(code.result, { node: n, file: f });
        anchors.set(code.receiver, { node: n, file: f });
      }
      if (ts.isObjectLiteralExpression(n)) site(n, f, "object");
      else if (ts.isArrayLiteralExpression(n)) site(n, f, "array");
      else if (functionLike(n) || classLike(n)) site(n, f, "closure");
      n.forEachChild(visit);
    };
    visit(f.source);
  }
  const fileAt = (n: Node): File | undefined => {
    let at: Node = n;
    while (at.parent) at = at.parent;
    return fileOfNode.get(at);
  };

  // The reads and calls whose type is primitive hold no reference; so do
  // the references to a parameter whose type is primitive, declared or,
  // unannotated, as TypeScript types its name. A binding's other references
  // hold what its sources hold, a primitive source holding none.
  const primitiveNodes = new Set<Node>();
  const libraryCallsOf = new Map<Node, LibraryCalls>();
  /** Of a call of a reviewed standard library method, whether it may call
   * each argument (`overlayCalls`), a spread one always, which it iterates. */
  const libraryCallsAt = (n: Node, args: readonly Node[]): boolean[] | null => {
    const c = libraryCallsOf.get(n);
    if (c === undefined) return null;
    return args.map((a, i) => ts.isSpreadElement(a) ||
      (c.params[i] ?? (c.rest && c.params.length > 0 ? c.params[c.params.length - 1] ?? true : true)));
  };
  const arrayMemberCalls = new Map<Node, string>();
  /** The calls of a method of another interface of the standard library. */
  const libraryMemberCalls = new Map<Node, string>();
  /** The calls of such a member TypeScript types an array of primitives. */
  const primitiveElementCalls = new Set<Node>();
  for (const f of files) {
    const asked: Node[] = [];
    const visit = (n: Node): void => {
      if (ts.isCallExpression(n) || ts.isPropertyAccessExpression(n) || ts.isElementAccessExpression(n)) asked.push(n);
      // An unannotated parameter's name, its type the contextual one.
      if (ts.isParameterDeclaration(n) && n.type === undefined && ts.isIdentifier(n.name)) asked.push(n.name);
      n.forEachChild(visit);
    };
    visit(f.source);
    reading.primitive(asked).forEach((p, i) => {
      const n = asked[i];
      if (p && n) primitiveNodes.add(n);
    });
    // The calls of a member of the standard library's arrays.
    const calls: Node[] = [];
    const names: Node[] = [];
    const callees = (n: Node): void => {
      if (ts.isCallExpression(n)) {
        const callee = unwrap(n.expression);
        if (ts.isPropertyAccessExpression(callee)) {
          calls.push(n);
          names.push(callee.name);
        }
      }
      n.forEachChild(callees);
    };
    callees(f.source);
    const members = reading.libraryMembers(names);
    const fresh = calls.filter((_, i) => { const m = members[i]; return !!m && m.array && freshArrayMember(m.name); });
    const primitive = reading.primitiveElements(fresh);
    members.forEach((m, i) => {
      const n = calls[i];
      if (m && n) {
        (m.array ? arrayMemberCalls : libraryMemberCalls).set(n, m.name);
        const calls = overlayCalls(m.owner, m.name);
        if (calls !== null) libraryCallsOf.set(n, calls);
      }
    });
    fresh.forEach((n, i) => { if (primitive[i]) primitiveElementCalls.add(n); });
  }

  // Scopes: the declaration an identifier names, lexically.
  const scopeNames = new Map<Node, Map<string, Node>>();
  const namesOf = (scope: Node): Map<string, Node> => {
    const known = scopeNames.get(scope);
    if (known) return known;
    const names = new Map<string, Node>();
    const add = (id: Node): void => {
      if (ts.isIdentifier(id) && !names.has(id.text)) names.set(id.text, id);
    };
    const statements = (list: readonly Node[]): void => {
      for (const s of list) {
        if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) boundNames(d.name).forEach(add);
        else if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isEnumDeclaration(s)) && s.name) add(s.name);
        else if (ts.isImportDeclaration(s)) {
          const clause = s.importClause;
          if (clause?.name) add(clause.name);
          const b = clause?.namedBindings;
          if (b && ts.isNamedImports(b)) for (const e of b.elements) add(e.name);
          else if (b && ts.isNamespaceImport(b)) add(b.name);
        }
      }
    };
    if (ts.isSourceFile(scope) || ts.isBlock(scope) || ts.isModuleBlock(scope)) statements(scope.statements);
    else if (ts.isCaseBlock(scope)) for (const c of scope.clauses) statements(c.statements);
    else if (functionLike(scope)) {
      for (const p of parametersOf(scope)) if (ts.isParameterDeclaration(p)) boundNames(p.name).forEach(add);
      if ((ts.isFunctionExpression(scope) || ts.isClassExpression(scope)) && scope.name) add(scope.name);
      const body = bodyOf(scope);
      if (body && ts.isBlock(body)) for (const [k, v] of namesOf(body)) if (!names.has(k)) names.set(k, v);
    } else if (ts.isClassExpression(scope) && scope.name) add(scope.name);
    else if (ts.isCatchClause(scope) && scope.variableDeclaration) boundNames(scope.variableDeclaration.name).forEach(add);
    else if ((ts.isForStatement(scope) || ts.isForOfStatement(scope) || ts.isForInStatement(scope)) && scope.initializer &&
        ts.isVariableDeclarationList(scope.initializer))
      for (const d of scope.initializer.declarations) boundNames(d.name).forEach(add);
    scopeNames.set(scope, names);
    return names;
  };
  const declOf = new Map<Node, Node | null>();
  const resolveName = (id: Node): Node | null => {
    if (!ts.isIdentifier(id)) return null;
    const known = declOf.get(id);
    if (known !== undefined) return known;
    let found: Node | null = null;
    for (let at: Node | undefined = id.parent; at && found === null; at = at.parent) found = namesOf(at).get(id.text) ?? null;
    declOf.set(id, found);
    return found;
  };
  /** The innermost code or file scope a declaration's binding is held in. */
  const holderOf = (decl: Node): Node | undefined => {
    for (let at: Node | undefined = decl.parent; at; at = at.parent) if (functionLike(at) || ts.isSourceFile(at)) return at;
    return undefined;
  };

  // The flow's sets.
  const sets = new Map<Key, FlowTokens>();
  const storageOf = (key: Key): FlowTokens => {
    let s = sets.get(key);
    if (!s) sets.set(key, s = new FlowTokens());
    return s;
  };
  const setOf = (key: Key): FlowTokens => {
    const tokens = storageOf(key);
    worklist.read(tokens);
    return tokens;
  };
  /** Each site's contents, by a key of its own. */
  const contentKeys = new Map<number, Key>();
  const contentKey = (i: number): Key => {
    let k = contentKeys.get(i);
    if (!k) {
      contentKeys.set(i, k = {});
      const s = sites[i];
      if (s) anchors.set(k, { node: s.node, file: s.file });
    }
    return k;
  };
  const contentOf = (i: number): FlowTokens => storageOf(contentKey(i));
  const contentsNow = (i: number): FlowTokens => setOf(contentKey(i));
  /** The identifiers bindings are declared at that hold a set. */
  const bindingDecls = new Set<Node>();
  let onBinding: ((decl: Node) => void) | undefined;
  const bindDecl = (decl: Node): void => {
    if (bindingDecls.has(decl)) return;
    bindingDecls.add(decl);
    onBinding?.(decl);
  };
  const addAll = (into: FlowTokens, from: Iterable<number>): void => {
    if (into === from) return;
    const size = into.size;
    if (from instanceof FlowTokens) into.copyFrom(from);
    else for (const t of from) into.add(t);
    if (into.size > size) worklist.grow(into);
  };
  const keys = new Map<number, Set<string>>();
  const anyKey = new Set<number>();
  const keyFact = (i: number): string => `keys:${i}`;
  const mayHoldKey = (i: number, key: string): boolean => {
    worklist.read(keyFact(i));
    return anyKey.has(i) || (keys.get(i)?.has(key) ?? false);
  };
  const addKey = (i: number, key: string | null): void => {
    if (key === null) {
      if (!anyKey.has(i)) { anyKey.add(i); worklist.grow(keyFact(i)); }
      return;
    }
    let s = keys.get(i);
    if (!s) keys.set(i, s = new Set());
    if (!s.has(key)) { s.add(key); worklist.grow(keyFact(i)); }
  };
  const incomingKeys = new Map<number, Set<string | null>>();
  const outsideTokens = (): number[] => components.map((_, c) => INCOMING + c);

  // The record: once the flow is solved, one more round states each set, what
  // the code's statements make it include, and the events, for the checks to
  // read (`recording`).
  let recording = false;
  type Row = { key: Key | null; module: string; pos: Span; from: SourceAst[] };
  const rows: Row[] = [];
  const rowOf = new Map<Key, number>();
  const firstFile = files[0];
  /** The value of a set of the flow. */
  const refOf = (key: Key): number => {
    const known = rowOf.get(key);
    if (known !== undefined) return known;
    const anchor = anchors.get(key);
    rowOf.set(key, rows.length);
    rows.push({ key, module: anchor?.file.location ?? firstFile?.location ?? "", pos: anchor ? span(anchor.file, anchor.node) : [0, 0], from: [] });
    return rows.length - 1;
  };
  /** The value of a node's set: a binding's, a parameter's, a call's. */
  const refNode = (n: Node): number => {
    const f = fileAt(n);
    if (f && !anchors.has(n)) anchors.set(n, { node: n, file: f });
    return refOf(n);
  };
  const sourceKey = (x: SourceAst): string => JSON.stringify(x);
  /** A set of the flow includes `x` by a statement of the code. */
  const include = (key: Key, x: SourceAst): void => {
    if (!recording) return;
    const row = rows[refOf(key)];
    if (row && !row.from.some((y) => sourceKey(y) === sourceKey(x))) row.from.push(x);
  };
  /** A value the code computes from others, at `node`. */
  const synthetic = (node: Node, f: File, from: SourceAst[]): number => {
    rows.push({ key: null, module: f.location, pos: span(f, node), from });
    return rows.length - 1;
  };
  const incomingSources = (): SourceAst[] => components.map((_, c) => ({ incoming: c }));
  /** Whether an import specifier names a module of the family, and which. */
  const moduleNamed = (from: File, specifier: string): File | null | undefined => {
    if (!specifier.startsWith(".")) return undefined;
    const base = resolve(dirname(from.absolute), specifier);
    for (const candidate of [base, base.replace(/\.js$/, ".ts"), base.replace(/\.mjs$/, ".mts"), base.replace(/\.cjs$/, ".cts"),
      `${base}.ts`, `${base}.tsx`, join(base, "index.ts")]) {
      const f = fileOf.get(candidate);
      if (f) return f;
    }
    return present(base) || sources.has(base) ? undefined : null;
  };
  const specifierText = (n: Node | undefined): string | null => n && ts.isStringLiteral(n) ? n.text : null;

  /** The code, binding or site a module's export `name` names, re-exports
   * followed; `outside` where it is code outside the family. */
  type Exported = { node: Node; file: File } | "outside" | null;
  const exportCache = new Map<string, Exported>();
  const exportOf = (f: File, name: string, seen: Set<string> = new Set()): Exported => {
    const key = `${f.absolute}\0${name}`;
    if (exportCache.has(key)) return exportCache.get(key) ?? null;
    if (seen.has(key)) return null;
    seen.add(key);
    let out: Exported = null;
    for (const s of f.source.statements) {
      if (out !== null) break;
      if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && exported(s) &&
          ((defaulted(s) && name === "default") || (!defaulted(s) && s.name?.text === name))) out = { node: s, file: f };
      else if (ts.isVariableStatement(s) && exported(s)) {
        for (const d of s.declarationList.declarations)
          for (const id of boundNames(d.name)) if (ts.isIdentifier(id) && id.text === name) out = { node: id, file: f };
      } else if (ts.isExportAssignment(s) && name === "default") out = { node: s.expression, file: f };
      else if (ts.isExportDeclaration(s) && !s.isTypeOnly) {
        const specifier = specifierText(s.moduleSpecifier);
        const target = specifier === null ? f : moduleNamed(f, specifier);
        const clause = s.exportClause;
        if (clause && ts.isNamedExports(clause)) {
          for (const e of clause.elements) {
            if (e.isTypeOnly || e.name.text !== name) continue;
            const local = e.propertyName && ts.isIdentifier(e.propertyName) ? e.propertyName.text : e.name.text;
            if (target === f) {
              const decl = namesOf(f.source).get(local);
              out = decl === undefined ? null : { node: decl, file: f };
            } else out = target ? exportOf(target, local, seen) : "outside";
          }
        } else if (!clause && target !== f && name !== "default") {
          const via = target ? exportOf(target, name, seen) : null;
          if (via !== null) out = via;
        }
      }
    }
    exportCache.set(key, out);
    return out;
  };
  /** The names a module exports of values. */
  const exportNames = (f: File, seen: Set<string> = new Set()): string[] => {
    if (seen.has(f.absolute)) return [];
    seen.add(f.absolute);
    const names: string[] = [];
    for (const s of f.source.statements) {
      if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && exported(s))
        names.push(defaulted(s) ? "default" : s.name?.text ?? "default");
      else if (ts.isVariableStatement(s) && exported(s)) {
        for (const d of s.declarationList.declarations) for (const id of boundNames(d.name)) if (ts.isIdentifier(id)) names.push(id.text);
      } else if (ts.isExportAssignment(s)) names.push("default");
      else if (ts.isExportDeclaration(s) && !s.isTypeOnly) {
        const clause = s.exportClause;
        if (clause && ts.isNamedExports(clause)) names.push(...clause.elements.filter((e) => !e.isTypeOnly).map((e) => e.name.text));
        else if (clause && ts.isNamespaceExport(clause)) names.push(clause.name.text);
        else {
          const specifier = specifierText(s.moduleSpecifier);
          const target = specifier === null ? null : moduleNamed(f, specifier);
          if (target) names.push(...exportNames(target, seen).filter((n) => n !== "default"));
        }
      }
    }
    return [...new Set(names)];
  };

  // Interfaces.
  // A component's entries, by the name its interface gives each.
  const entryNodes = new Map<number, Map<string, Node>>();
  const entriesOf = (c: number): Map<string, Node> => {
    let m = entryNodes.get(c);
    if (!m) entryNodes.set(c, m = new Map());
    return m;
  };
  /** The codes an exported value names: a function's, a class's constructor
   * and members, a closure a binding is initialized with. */
  const exportedCodes = (target: Exported, name: string, into: Map<string, Node>): void => {
    if (target === null || target === "outside") return;
    const n = target.node;
    if (ts.isFunctionDeclaration(n)) into.set(name, n);
    else if (classLike(n)) {
      into.set(name, n);
      if (ts.isClassDeclaration(n) || ts.isClassExpression(n))
        for (const m of n.members) if (publicMethod(m)) into.set(`${name}.${memberLabel(m)}`, m);
    } else if (ts.isIdentifier(n) && n.parent && ts.isVariableDeclaration(n.parent) && n.parent.initializer) {
      const init = unwrap(n.parent.initializer);
      if (functionLike(init) || classLike(init)) exportedCodes({ node: init, file: target.file }, name, into);
    } else {
      const init = unwrap(n);
      if (init !== n && (functionLike(init) || classLike(init))) exportedCodes({ node: init, file: target.file }, name, into);
    }
  };
  for (const f of files) {
    const own = new Map<string, Node>();
    for (const name of exportNames(f)) exportedCodes(exportOf(f, name), name, own);
    for (const [name, n] of own) if (fileAt(n) === f) entriesOf(f.module).set(name, n);
  }
  // A module exporting a binding whose value is no code it declares but
  // names one of its functions or classes (`export const g = f`,
  // `export const api = { f }`) gives that code out under the binding's
  // type, which no entry states: its interface is unknown.
  for (const f of files) {
    const declared = new Set(f.source.statements.flatMap((s) =>
      (ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && s.name ? [s.name.text] : []));
    const named = (n: Node): string | null => {
      if (ts.isIdentifier(n) && declared.has(n.text)) {
        const p = n.parent;
        const label = p !== undefined && ((ts.isPropertyAccessExpression(p) && p.name === n) ||
          (ts.isPropertyAssignment(p) && p.name === n) || (ts.isMethodDeclaration(p) && p.name === n));
        if (!label) return n.text;
      }
      let found: string | null = null;
      n.forEachChild((c: Node) => { found ??= named(c); });
      return found;
    };
    for (const s of f.source.statements) {
      if (!ts.isVariableStatement(s) || !exported(s)) continue;
      for (const d of s.declarationList.declarations) {
        if (!d.initializer) continue;
        const init = unwrap(d.initializer);
        if (functionLike(init) || classLike(init)) continue;
        const x = named(d.initializer);
        const component = components[f.module];
        if (x !== null && component && "known" in component.interface)
          component.interface = { unknown: { reason: `${f.location} exports ${d.name.getText(f.source)}, a value naming its code ${x}, which no entry states` } };
      }
    }
  }
  if (packageIndex !== null)
    for (const m of entryModules) {
      const f = fileOf.get(m);
      if (f) for (const name of exportNames(f)) exportedCodes(exportOf(f, name), name, entriesOf(packageIndex));
    }
  for (const [n, c] of classComponent) {
    if (!(ts.isClassDeclaration(n) || ts.isClassExpression(n))) continue;
    const e = entriesOf(c);
    const ctor = n.members.find((m) => ts.isConstructorDeclaration(m));
    e.set("constructor", ctor ?? n);
    for (const m of n.members) if (publicMethod(m)) e.set(memberLabel(m), m);
  }

  // Members: entries and escaping codes, each component's.
  const members = new Map<number, Set<Node>>();
  const memberOf = (c: number): Set<Node> => {
    let s = members.get(c);
    if (!s) members.set(c, s = new Set([...entriesOf(c).values()].map((n) => ts.isClassDeclaration(n) || ts.isClassExpression(n)
      ? n.members.find((m) => ts.isConstructorDeclaration(m)) ?? n : n)));
    return s;
  };
  const marks = new Map<string, Mark>();
  const markOf = (s: number, c: number): Mark => {
    const key = `${s}:${c}`;
    worklist.read(key);
    return marks.get(key) ?? "local";
  };
  const raise = (s: number, c: number, m: Mark): void => {
    const key = `${s}:${c}`;
    if (rank(marks.get(key) ?? "local") >= rank(m)) return;
    marks.set(key, m);
    worklist.grow(key);
  };

  // Read-only types, read from the syntax: primitives and literals, `unknown`,
  // read-only arrays and tuples of such types, records whose every member is a
  // readonly field of such a type, unions and intersections of such types, a
  // sealed handle, and a named type of the family whose definition is one.
  const typeDecl = (f: File, name: string): { node: Node; file: File } | null => {
    for (const s of f.source.statements)
      if ((ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s)) && s.name.text === name) return { node: s, file: f };
    for (const s of f.source.statements) {
      if (!ts.isImportDeclaration(s)) continue;
      const b = s.importClause?.namedBindings;
      if (!b || !ts.isNamedImports(b)) continue;
      for (const e of b.elements) {
        if (e.name.text !== name) continue;
        const specifier = specifierText(s.moduleSpecifier);
        const target = specifier === null ? null : moduleNamed(f, specifier);
        const imported = e.propertyName && ts.isIdentifier(e.propertyName) ? e.propertyName.text : name;
        return target ? typeDecl(target, imported) : null;
      }
    }
    return null;
  };
  /** **A declared type's shape**, as the wire states it (`TypeShapeAst`):
   * what decides whether it is read-only, each named type of the family by
   * its index in `types`. */
  const typeRows: ComponentsAst["types"] = [];
  const typeIndex = new Map<Node, number>();
  const shapeOf = (t: Node | undefined, f: File, depth: number = 0): TypeShapeAst | null => {
    if (t === undefined) return null;
    if (depth > 24) return "other";
    const k = t.kind;
    if (k === ts.SyntaxKind.UnknownKeyword) return "unknown";
    if (k === ts.SyntaxKind.NumberKeyword || k === ts.SyntaxKind.StringKeyword || k === ts.SyntaxKind.BooleanKeyword ||
        k === ts.SyntaxKind.BigIntKeyword || k === ts.SyntaxKind.SymbolKeyword || k === ts.SyntaxKind.UndefinedKeyword ||
        k === ts.SyntaxKind.VoidKeyword || k === ts.SyntaxKind.NeverKeyword || ts.isLiteralTypeNode(t) || ts.isTemplateLiteralTypeNode(t))
      return "primitive";
    const inner = (x: Node): TypeShapeAst => shapeOf(x, f, depth + 1) ?? "other";
    const elements = (x: Node): TypeShapeAst[] => ts.isTupleTypeNode(x)
      ? x.elements.map((e) => inner(ts.isNamedTupleMember(e) ? e.type : e)) : [];
    if (ts.isParenthesizedTypeNode(t)) return inner(t.type);
    if (ts.isTypeOperatorNode(t) && t.operator === ts.SyntaxKind.ReadonlyKeyword) {
      const x = t.type;
      return ts.isArrayTypeNode(x) ? { readonlyArray: inner(x.elementType) }
        : ts.isTupleTypeNode(x) ? { tuple: { readonly: true, elements: elements(x) } } : "other";
    }
    if (ts.isArrayTypeNode(t)) return { array: inner(t.elementType) };
    if (ts.isTupleTypeNode(t)) return { tuple: { readonly: false, elements: elements(t) } };
    if (ts.isUnionTypeNode(t)) return { union: t.types.map(inner) };
    if (ts.isIntersectionTypeNode(t)) return { intersection: t.types.map(inner) };
    if (ts.isTypeLiteralNode(t)) return { record: t.members.map((m) => memberShape(m, f, depth)) };
    if (ts.isFunctionTypeNode(t)) return "function";
    if (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName)) {
      const name = t.typeName.text, args = t.typeArguments ?? [];
      if (name === "ReadonlyArray" && args.length === 1 && args[0]) return { readonlyArray: inner(args[0]) };
      if (args.length > 0) return "other";
      const d = typeDecl(f, name);
      if (d === null) return "other";
      const known = typeIndex.get(d.node);
      if (known !== undefined) return { named: known };
      const index = typeRows.length;
      typeIndex.set(d.node, index);
      typeRows.push({ module: d.file.location, name, pos: span(d.file, d.node), definition: "other" });
      const definition: TypeShapeAst = representationTags(leading(d.file.source, d.node)).length > 0 ? "sealed"
        : ts.isTypeAliasDeclaration(d.node) ? shapeOf(d.node.type, d.file, depth + 1) ?? "other"
        : ts.isInterfaceDeclaration(d.node) && !d.node.heritageClauses?.length
          ? { record: d.node.members.map((m) => memberShape(m, d.file, depth)) } : "other";
      const row = typeRows[index];
      if (row) row.definition = definition;
      return { named: index };
    }
    return "other";
  };
  /** A member of a record type: a property or an index signature, with its
   * `readonly` modifier and type; any other member. */
  const memberShape = (m: Node, f: File, depth: number): { readonly: boolean; field: boolean; type: TypeShapeAst } => {
    const field = ts.isPropertySignatureDeclaration(m) || ts.isIndexSignatureDeclaration(m);
    const ro = (ts.isPropertySignatureDeclaration(m) || ts.isIndexSignatureDeclaration(m)) &&
      !!m.modifiers?.some((x) => x.kind === ts.SyntaxKind.ReadonlyKeyword);
    const type = ts.isPropertySignatureDeclaration(m) || ts.isIndexSignatureDeclaration(m) ? shapeOf(m.type, f, depth + 1) ?? "other" : "other";
    return { readonly: ro, field, type };
  };
  /** **A read-only type** (`shapeReadOnly`, ComponentChecks.readOnlyShape). */
  const readOnly = (t: Node | undefined, f: File): boolean => shapeReadOnly(shapeOf(t, f), typeRows);
  const typeOfParameter = (p: Node | undefined): TypeNode | undefined => p && ts.isParameterDeclaration(p) ? p.type : undefined;
  const resultType = (n: Node): TypeNode | undefined =>
    ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
    ts.isGetAccessorDeclaration(n) ? n.type : undefined;

  // Crossings grow during solving. The recording pass adds their references.
  type FlowCrossing = CrossingAst & { tokens: FlowTokens; node: Node | null; via: "result" | "argument" | "throw" | "store" | null };
  const crossings = new Map<string, FlowCrossing>();
  const cross = (f: File, at: Node, c: number, direction: "in" | "out", position: PositionAst, ro: boolean,
      tokens: FlowValues | null, valueNode: Node | null, ref: number | null): void => {
    const key = `${f.absolute}:${at.getStart(f.source)}:${at.end}:${c}:${direction}:${JSON.stringify(position)}`;
    const via = direction === "in" ? null : typeof position === "object" && "result" in position ? "result"
      : typeof position === "object" && "argument" in position ? "argument" : position === "thrown" ? "throw" : "store";
    const held = crossings.get(key);
    if (held) {
      if (tokens) addAll(held.tokens, tokens);
      if (recording && ref !== null && held.value === null) held.value = ref;
      return;
    }
    const crossing: FlowCrossing = { module: f.location, at: span(f, at), component: c, direction, position, readOnly: ro,
      value: recording ? ref : null, tokens: new FlowTokens(tokens ?? []), node: valueNode, via };
    crossings.set(key, crossing);
    if (!recording && direction === "out") {
      let observed = 0;
      worklist.add(() => {
        worklist.read(crossing.tokens);
        for (const t of crossing.tokens.since(observed)) {
          const s = sites[t];
          if (s && within(s.component, c)) raise(t, c, ro ? "exposed" : "released");
        }
        observed = crossing.tokens.size;
      });
    }
  };

  /** The values thrown, by a key of its own. */
  const thrownKey: Key = {};
  if (firstFile) anchors.set(thrownKey, { node: firstFile.source, file: firstFile });
  /** The events the record states. */
  const events: Pick<ComponentsAst, "stores" | "calls" | "throws" | "catches" | "holds" | "exports"> =
    { stores: [], calls: [], throws: [], catches: [], holds: [], exports: [] };
  const codeAt = (n: Node): Code | undefined => {
    for (let at: Node | undefined = n.parent; at; at = at.parent) {
      const c = codeOf.get(at);
      if (c && !ts.isArrowFunction(at)) return c;
    }
    return undefined;
  };
  const enclosingCode = (n: Node): Code | undefined => {
    for (let at: Node | undefined = n.parent; at; at = at.parent) {
      const c = codeOf.get(at);
      if (c) return c;
    }
    return undefined;
  };
  const componentAt = (n: Node, f: File): number => innermost(n, f);
  /** The components a code is outside of, given a callee's tokens: those it
   * may enter from outside. */
  /** The components a value may enter from outside, at either position. */
  const incomingOf = (tokens: Iterable<number>): number[] =>
    [...new Set([...tokens].filter((t) => t >= INCOMING).map(componentOfToken))];
  const writableIncoming = (tokens: Iterable<number>): number[] =>
    [...tokens].filter((t) => t >= INCOMING && t < INCOMING_RO).map((t) => t - INCOMING);
  const readOnlyIncoming = (tokens: Iterable<number>): number[] => [...tokens].filter((t) => t >= INCOMING_RO).map((t) => t - INCOMING_RO);
  const sitesOf = (tokens: Iterable<number>): number[] => [...tokens].filter((t) => t < INCOMING);
  /** Read only newly added contents from each of the given sites. */
  const readInto = (out: FlowTokens, tokens: Iterable<number>): void => {
    for (const t of tokens) {
      if (t >= INCOMING) out.add(t);
      else {
        const contents = contentsNow(t);
        if (out !== contents) out.copyFrom(contents);
      }
    }
  };
  // All transfers that read a stored value share its projection through
  // site contents. Changes to either the value or its contents update it.
  const readViews = new WeakMap<FlowTokens, FlowTokens>();
  const reads = (tokens: FlowValues): FlowValues => {
    if (worklist.active && tokens instanceof FlowTokens) {
      let view = readViews.get(tokens);
      if (view === undefined) {
        const projected = new FlowTokens();
        view = projected;
        readViews.set(tokens, projected);
        worklist.run(() => {
          worklist.read(tokens);
          const size = projected.size;
          readInto(projected, tokens);
          if (projected.size > size) worklist.grow(projected);
        });
      }
      worklist.read(view);
      return view;
    }
    const out = new Set<number>();
    for (const t of tokens) {
      if (t >= INCOMING) out.add(t);
      else for (const x of contentsNow(t)) out.add(x);
    }
    return out;
  };

  /** The tokens of an expression's value. */
  // An expression is computed once per rule evaluation.
  const ruleValues = new Map<Node, FlowValues>();
  const value = (e: Node | undefined, f: File): FlowValues => {
    if (e === undefined) return new Set();
    const held = ruleValues.get(e);
    if (held) return held;
    const computed = valueNow(e, f);
    ruleValues.set(e, computed);
    return computed;
  };
  const valueNow = (e: Node, f: File): FlowValues => {
    const x = unwrap(e);
    if (primitiveNodes.has(x)) return new Set();
    if (ts.isIdentifier(x)) return primitiveParameter(x) ? new Set() : identifierValue(x, f);
    if (x.kind === ts.SyntaxKind.ThisKeyword) {
      const c = codeAt(x);
      return c ? setOf(c.receiver) : new Set();
    }
    if (ts.isObjectLiteralExpression(x) || ts.isArrayLiteralExpression(x) || functionLike(x) || classLike(x))
      return new Set([site(x, f, ts.isObjectLiteralExpression(x) ? "object" : ts.isArrayLiteralExpression(x) ? "array" : "closure")]);
    if (ts.isPropertyAccessExpression(x) || ts.isElementAccessExpression(x)) return reads(value(x.expression, f));
    if (ts.isCallExpression(x) || ts.isNewExpression(x)) return setOf(x);
    if (ts.isConditionalExpression(x)) return new Set([...value(x.whenTrue, f), ...value(x.whenFalse, f)]);
    if (ts.isBinaryExpression(x)) {
      const op = x.operatorToken.kind;
      if (op === ts.SyntaxKind.EqualsToken || op === ts.SyntaxKind.CommaToken) return value(x.right, f);
      if (op === ts.SyntaxKind.QuestionQuestionToken || op === ts.SyntaxKind.BarBarToken || op === ts.SyntaxKind.AmpersandAmpersandToken ||
          op === ts.SyntaxKind.QuestionQuestionEqualsToken || op === ts.SyntaxKind.BarBarEqualsToken ||
          op === ts.SyntaxKind.AmpersandAmpersandEqualsToken)
        return new Set([...value(x.left, f), ...value(x.right, f)]);
      return new Set();
    }
    if (ts.isAwaitExpression(x) || ts.isYieldExpression(x)) return new Set(outsideTokens());
    return new Set();
  };
  const identifierValue = (id: Node, f: File): FlowValues => {
    const decl = resolveName(id);
    if (decl === null) return new Set();
    const owner = decl.parent;
    if (owner && (ts.isFunctionDeclaration(owner) || ts.isClassDeclaration(owner)) && owner.name === decl)
      return new Set([site(owner, fileAt(owner) ?? f, "closure")]);
    if (owner && (ts.isImportSpecifier(owner) || ts.isImportClause(owner))) {
      const imp = ts.isImportSpecifier(owner) ? owner.parent?.parent?.parent : owner.parent;
      const specifier = imp && ts.isImportDeclaration(imp) ? specifierText(imp.moduleSpecifier) : null;
      const target = specifier === null ? null : moduleNamed(f, specifier);
      if (!target) return new Set(outsideTokens());
      const name = ts.isImportSpecifier(owner) ? (owner.propertyName && ts.isIdentifier(owner.propertyName) ? owner.propertyName.text : owner.name.text) : "default";
      const exportedNode = exportOf(target, name);
      if (exportedNode === null) return new Set();
      if (exportedNode === "outside") return new Set(outsideTokens());
      return ts.isIdentifier(exportedNode.node) ? identifierValue(exportedNode.node, exportedNode.file) : value(exportedNode.node, exportedNode.file);
    }
    if (owner && ts.isNamespaceImport(owner)) return new Set(outsideTokens());
    return setOf(decl);
  };

  /** Whether a reference names a parameter whose declared type is
   * primitive: a primitive keyword or a literal type, or a union of them. */
  const primitiveType = (t: Node | undefined): boolean => {
    if (t === undefined) return false;
    const k = t.kind;
    if (k === ts.SyntaxKind.NumberKeyword || k === ts.SyntaxKind.StringKeyword || k === ts.SyntaxKind.BooleanKeyword ||
        k === ts.SyntaxKind.BigIntKeyword || k === ts.SyntaxKind.SymbolKeyword || k === ts.SyntaxKind.UndefinedKeyword ||
        k === ts.SyntaxKind.NeverKeyword || ts.isLiteralTypeNode(t) || ts.isTemplateLiteralTypeNode(t))
      return true;
    if (ts.isParenthesizedTypeNode(t)) return primitiveType(t.type);
    return ts.isUnionTypeNode(t) && t.types.every(primitiveType);
  };
  const primitiveParameter = (id: Node): boolean => {
    const decl = resolveName(id);
    const owner = decl?.parent;
    if (!owner || !ts.isParameterDeclaration(owner) || owner.name !== decl) return false;
    if (owner.type === undefined) return primitiveNodes.has(owner.name);
    const f = fileAt(owner);
    return primitiveType(owner.type) || (f !== undefined && shapePrimitive(shapeOf(owner.type, f), typeRows));
  };
  /** **An expression's value in the record**: what the expression's form
   * makes it include, as `valueNow` computes it. */
  const exprRefs = new Map<Node, number>();
  const exprRef = (e: Node | undefined, f: File): number => {
    if (e === undefined) return synthetic(f.source, f, []);
    const known = exprRefs.get(e);
    if (known !== undefined) return known;
    const x = unwrap(e);
    const sources = (): SourceAst[] => {
      if (primitiveNodes.has(x)) return [];
      if (ts.isIdentifier(x)) return primitiveParameter(x) ? [] : identifierSources(x, f);
      if (x.kind === ts.SyntaxKind.ThisKeyword) {
        const c = codeAt(x);
        return c ? [{ value: refOf(c.receiver) }] : [];
      }
      if (ts.isObjectLiteralExpression(x) || ts.isArrayLiteralExpression(x) || functionLike(x) || classLike(x))
        return [{ site: site(x, f, ts.isObjectLiteralExpression(x) ? "object" : ts.isArrayLiteralExpression(x) ? "array" : "closure") }];
      if (ts.isPropertyAccessExpression(x) || ts.isElementAccessExpression(x)) return [{ read: exprRef(x.expression, f) }];
      if (ts.isConditionalExpression(x)) return [{ value: exprRef(x.whenTrue, f) }, { value: exprRef(x.whenFalse, f) }];
      if (ts.isBinaryExpression(x)) {
        const op = x.operatorToken.kind;
        if (op === ts.SyntaxKind.EqualsToken || op === ts.SyntaxKind.CommaToken) return [{ value: exprRef(x.right, f) }];
        if (op === ts.SyntaxKind.QuestionQuestionToken || op === ts.SyntaxKind.BarBarToken || op === ts.SyntaxKind.AmpersandAmpersandToken ||
            op === ts.SyntaxKind.QuestionQuestionEqualsToken || op === ts.SyntaxKind.BarBarEqualsToken ||
            op === ts.SyntaxKind.AmpersandAmpersandEqualsToken)
          return [{ value: exprRef(x.left, f) }, { value: exprRef(x.right, f) }];
        return [];
      }
      if (ts.isAwaitExpression(x) || ts.isYieldExpression(x)) return incomingSources();
      return [];
    };
    const ref = !primitiveNodes.has(x) && (ts.isCallExpression(x) || ts.isNewExpression(x)) ? refNode(x) : synthetic(x, f, sources());
    exprRefs.set(e, ref);
    return ref;
  };
  const identifierSources = (id: Node, f: File): SourceAst[] => {
    const decl = resolveName(id);
    if (decl === null) return [];
    const owner = decl.parent;
    if (owner && (ts.isFunctionDeclaration(owner) || ts.isClassDeclaration(owner)) && owner.name === decl)
      return [{ site: site(owner, fileAt(owner) ?? f, "closure") }];
    if (owner && (ts.isImportSpecifier(owner) || ts.isImportClause(owner))) {
      const imp = ts.isImportSpecifier(owner) ? owner.parent?.parent?.parent : owner.parent;
      const specifier = imp && ts.isImportDeclaration(imp) ? specifierText(imp.moduleSpecifier) : null;
      const target = specifier === null ? null : moduleNamed(f, specifier);
      if (!target) return incomingSources();
      const name = ts.isImportSpecifier(owner) ? (owner.propertyName && ts.isIdentifier(owner.propertyName) ? owner.propertyName.text : owner.name.text) : "default";
      const exportedNode = exportOf(target, name);
      if (exportedNode === null) return [];
      if (exportedNode === "outside") return incomingSources();
      return ts.isIdentifier(exportedNode.node) ? identifierSources(exportedNode.node, exportedNode.file)
        : [{ value: exprRef(exportedNode.node, exportedNode.file) }];
    }
    if (owner && ts.isNamespaceImport(owner)) return incomingSources();
    return [{ value: refNode(decl) }];
  };

  /** Bind a binding name to tokens: each name the whole value, or what a
   * pattern reads of it. */
  const bind = (name: Node, tokens: FlowValues, f: File, ref: () => number): void => {
    if (ts.isIdentifier(name)) {
      bindDecl(name);
      addAll(storageOf(name), tokens);
      if (recording) {
        refNode(name);
        include(name, { value: ref() });
      }
    } else if (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name)) {
      const contents = reads(tokens);
      for (const e of name.elements) if (ts.isBindingElement(e)) {
        const rest = e.dotDotDotToken ? site(e, f, ts.isArrayBindingPattern(name) ? "array" : "object") : null;
        const read = rest !== null ? new Set([...contents, rest]) : contents;
        if (rest !== null) {
          addAll(contentOf(rest), contents);
          if (recording) events.stores.push({ module: f.location, at: span(f, e), component: componentAt(e, f),
            receiver: synthetic(e, f, [{ site: rest }]), key: null, element: true,
            stored: synthetic(e, f, [{ read: ref() }]), initial: true });
        }
        if (e.name) bind(e.name, e.initializer ? new Set([...read, ...value(e.initializer, f)]) : read, f, () => synthetic(e, f,
          [{ read: ref() }, ...(rest !== null ? [{ site: rest }] : []), ...(e.initializer ? [{ value: exprRef(e.initializer, f) }] : [])]));
      }
    }
  };
  /** The tokens a call's callee may be: the closures it may run, and the
   * components it may enter from outside. */
  const calleeTokens = (callee: Node, f: File): { tokens: FlowValues; receiver: FlowValues | null } => {
    const x = unwrap(callee);
    if (ts.isPropertyAccessExpression(x) || ts.isElementAccessExpression(x)) {
      const receiver = value(x.expression, f);
      const contents = reads(receiver);
      const tokens = contents instanceof FlowTokens ? new Set(contents) : contents;
      const name = ts.isPropertyAccessExpression(x) ? x.name.text : nameText(x.argumentExpression);
      // A method of a class whose instance the receiver may be, or of the
      // class itself where the receiver is a class value.
      for (const t of sitesOf(receiver)) {
        const s = sites[t];
        if (!s) continue;
        const cls = s.kind === "instance" ? instanceClass(t) : classLike(s.node) ? s.node : undefined;
        const statics = s.kind !== "instance";
        for (let c: Node | undefined = cls; c && (ts.isClassDeclaration(c) || ts.isClassExpression(c)); c = baseOf(c, f))
          for (const m of c.members)
            if (functionLike(m) && !ts.isConstructorDeclaration(m) && nameText(memberName(m)) === name && isStatic(m) === statics)
              tokens.add(site(m, fileAt(m) ?? f, "closure"));
      }
      return { tokens, receiver };
    }
    return { tokens: value(x, f), receiver: null };
  };
  const classOfInstance = new Map<number, Node>();
  const instanceClass = (t: number): Node | undefined => {
    worklist.read(`instance:${t}`);
    return classOfInstance.get(t);
  };
  const baseOf = (c: Node, f: File): Node | undefined => {
    if (!(ts.isClassDeclaration(c) || ts.isClassExpression(c))) return undefined;
    for (const h of c.heritageClauses ?? [])
      if (h.token === ts.SyntaxKind.ExtendsKeyword)
        for (const t of h.types) for (const s of sitesOf(value(t.expression, fileAt(c) ?? f))) {
          const n = sites[s]?.node;
          if (n && classLike(n)) return n;
        }
    return undefined;
  };
  const constructorOf = (c: Node): Node =>
    (ts.isClassDeclaration(c) || ts.isClassExpression(c) ? c.members.find((m) => ts.isConstructorDeclaration(m)) : undefined) ?? c;
  /** A call of a code of the family: its parameters include its arguments,
   * its receiver the call's, and the call's result its result. The code it
   * runs, or null. */
  const callCode = (target: Node, args: readonly Node[], f: File, call: Node, receiver: FlowValues | null): Code | null => {
    const code = codeOf.get(target);
    const ctor = classLike(target) ? constructorOf(target) : target;
    const c = codeOf.get(ctor) ?? code;
    if (c) {
      args.forEach((a, i) => {
        if (ts.isSpreadElement(a)) for (const p of c.params) bindParameter(p, reads(value(a.expression, f)), c.file);
        else {
          const p = c.params[i];
          if (p) bindParameter(p, value(a, f), c.file);
        }
      });
      if (receiver) addAll(storageOf(c.receiver), receiver);
      if (!classLike(target)) addAll(storageOf(call), setOf(c.result));
    }
    return c ?? null;
  };
  const bindParameter = (p: Node, tokens: FlowValues, f: File): void => {
    if (!ts.isParameterDeclaration(p)) return;
    addAll(storageOf(p), tokens);
    bind(p.name, tokens, f, () => refNode(p));
  };
  /** The declared parameter types of a callee that is a parameter or a
   * binding of function type. */
  const calleeParameterTypes = (callee: Node): readonly (TypeNode | undefined)[] => {
    const x = unwrap(callee);
    const decl = ts.isIdentifier(x) ? resolveName(x) : null;
    const owner = decl?.parent;
    const type = owner && (ts.isParameterDeclaration(owner) || ts.isVariableDeclaration(owner)) ? owner.type : undefined;
    const fn = type && ts.isParenthesizedTypeNode(type) ? type.type : type;
    return fn && ts.isFunctionTypeNode(fn) ? fn.parameters.map((p) => typeOfParameter(p)) : [];
  };

  /** The inclusions and crossings of a single statement or expression. */
  const compileTransfer = (n: Node, f: File): FlowRule | undefined => {
    if (ts.isVariableDeclaration(n) && n.initializer)
      return () => bind(n.name, value(n.initializer, f), f, () => exprRef(n.initializer, f));
    if (ts.isBinaryExpression(n)) return () => {
      const op = n.operatorToken.kind;
      const target = unwrap(n.left);
      const assigns = op === ts.SyntaxKind.EqualsToken || op === ts.SyntaxKind.QuestionQuestionEqualsToken ||
        op === ts.SyntaxKind.BarBarEqualsToken || op === ts.SyntaxKind.AmpersandAmpersandEqualsToken;
      const writes = op >= ts.SyntaxKind.FirstAssignment && op <= ts.SyntaxKind.LastAssignment;
      if (writes && ts.isIdentifier(target) && assigns) {
        const decl = resolveName(target);
        if (decl) {
          bindDecl(decl);
          addAll(storageOf(decl), value(n.right, f));
          if (recording) {
            refNode(decl);
            include(decl, { value: exprRef(n.right, f) });
          }
        }
      } else if (writes && (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)))
        store(target.expression, ts.isPropertyAccessExpression(target) ? target.name.text : nameText(target.argumentExpression),
          assigns ? value(n.right, f) : new Set(), f, n, assigns ? () => exprRef(n.right, f) : null);
    };
    if (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n) || ts.isDeleteExpression(n)) return () => {
      const target = unwrap(ts.isDeleteExpression(n) ? n.expression : n.operand);
      if (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target))
        store(target.expression, ts.isPropertyAccessExpression(target) ? target.name.text : nameText(target.argumentExpression), new Set(), f, n, null);
    };
    if (ts.isObjectLiteralExpression(n)) return () => {
      const s = site(n, f, "object");
      // Each property an initial value of the record allocated here.
      const initial = (p: Node, key: string | null, stored: () => number): void => {
        if (recording) events.stores.push({ module: f.location, at: span(f, p), component: componentAt(p, f), receiver: exprRef(n, f),
          key, element: false, stored: stored(), initial: true });
      };
      for (const p of n.properties) {
        if (ts.isPropertyAssignment(p)) {
          addKey(s, nameText(p.name));
          addAll(contentOf(s), value(p.initializer, f));
          initial(p, nameText(p.name), () => exprRef(p.initializer, f));
        } else if (ts.isShorthandPropertyAssignment(p)) {
          addKey(s, nameText(p.name));
          addAll(contentOf(s), value(p.name, f));
          initial(p, nameText(p.name), () => exprRef(p.name, f));
        } else if (ts.isSpreadAssignment(p)) {
          addKey(s, null);
          addAll(contentOf(s), reads(value(p.expression, f)));
          initial(p, null, () => synthetic(p, f, [{ read: exprRef(p.expression, f) }]));
        } else if (functionLike(p)) {
          const key = ts.isMethodDeclaration(p) || ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p) ? nameText(p.name) : null;
          addKey(s, key);
          const closure = site(p, f, "closure");
          addAll(contentOf(s), [closure]);
          initial(p, key, () => synthetic(p, f, [{ site: closure }]));
          const code = codeOf.get(p);
          if (code) {
            addAll(storageOf(code.receiver), [s]);
            include(code.receiver, { site: s });
          }
        }
      }
    };
    if (ts.isArrayLiteralExpression(n)) return () => {
      const s = site(n, f, "array");
      for (const e of n.elements) {
        addAll(contentOf(s), ts.isSpreadElement(e) ? reads(value(e.expression, f)) : value(e, f));
        if (recording) events.stores.push({ module: f.location, at: span(f, e), component: componentAt(e, f), receiver: exprRef(n, f),
          key: null, element: true, initial: true,
          stored: ts.isSpreadElement(e) ? synthetic(e, f, [{ read: exprRef(e.expression, f) }]) : exprRef(e, f) });
      }
    };
    if (ts.isReturnStatement(n) && n.expression) return () => {
      const c = enclosingCode(n);
      if (c) {
        addAll(storageOf(c.result), value(n.expression, f));
        if (recording) include(c.result, { value: exprRef(n.expression, f) });
      }
    };
    if (ts.isArrowFunction(n) && !ts.isBlock(n.body)) return () => {
      const c = codeOf.get(n);
      if (c) {
        addAll(storageOf(c.result), value(n.body, f));
        if (recording) include(c.result, { value: exprRef(n.body, f) });
      }
    };
    if (ts.isThrowStatement(n)) return () => {
      const tokens = value(n.expression, f);
      addAll(storageOf(thrownKey), tokens);
      const ref = recording ? exprRef(n.expression, f) : -1;
      if (recording) {
        include(thrownKey, { value: ref });
        events.throws.push({ module: f.location, at: span(f, n), component: componentAt(n, f), value: ref });
      }
      for (const c of enclosing(componentAt(n, f))) cross(f, n, c, "out", "thrown", false, tokens, n.expression, ref);
    };
    if (ts.isCatchClause(n) && n.variableDeclaration) {
      const decl = n.variableDeclaration;
      return () => {
        const comps = enclosing(componentAt(n, f));
        const tokens = new Set([...setOf(thrownKey), ...comps.map((c) => INCOMING + c)]);
        const ref = recording ? synthetic(decl, f, [{ value: refOf(thrownKey) }, ...comps.map((c) => ({ incoming: c }))]) : -1;
        bind(decl.name, tokens, f, () => ref);
        if (recording) events.catches.push({ module: f.location, at: span(f, decl), component: componentAt(n, f), value: ref });
        for (const c of comps) cross(f, decl, c, "in", "caught", false, tokens, null, ref);
      };
    }
    if (ts.isForOfStatement(n) && ts.isVariableDeclarationList(n.initializer)) {
      const { declarations } = n.initializer;
      return () => {
        for (const d of declarations)
          bind(d.name, reads(value(n.expression, f)), f, () => synthetic(n.expression, f, [{ read: exprRef(n.expression, f) }]));
      };
    }
    if (ts.isPropertyDeclaration(n) && n.initializer && n.parent && classLike(n.parent)) return () => {
      // A field's initial value, in the class's instances or, static, in
      // the class itself.
      const statics = !!n.modifiers?.some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
      const holder = instancesKey(n.parent);
      const holders = statics ? new Set([site(n.parent, f, "closure")]) : setOf(holder);
      for (const t of sitesOf(holders)) {
        addKey(t, nameText(n.name));
        addAll(contentOf(t), value(n.initializer, f));
      }
      if (recording) events.stores.push({ module: f.location, at: span(f, n), component: componentAt(n, f),
        receiver: statics ? synthetic(n, f, [{ site: site(n.parent, f, "closure") }]) : refOf(holder),
        key: nameText(n.name), element: false, stored: exprRef(n.initializer, f), initial: true });
    };
    if (ts.isCallExpression(n) || ts.isNewExpression(n)) return () => call(n, f);
    return undefined;
  };
  /** A class's instances, by a key of its own. */
  const instanceKeys = new Map<Node, Key>();
  const instancesKey = (c: Node): Key => {
    let k = instanceKeys.get(c);
    if (!k) {
      instanceKeys.set(c, k = {});
      const f = fileAt(c);
      if (f) anchors.set(k, { node: c, file: f });
    }
    return k;
  };
  const store = (receiverExpr: Node, key: string | null, tokens: FlowValues, f: File, at: Node,
      stored: (() => number) | null): void => {
    const receiver = value(receiverExpr, f);
    const ref = recording && stored !== null ? stored() : null;
    if (recording) events.stores.push({ module: f.location, at: span(f, at), component: componentAt(at, f),
      receiver: exprRef(receiverExpr, f), key, element: false, stored: ref, initial: false });
    for (const t of receiver) {
      if (t >= INCOMING) {
        const c = componentOfToken(t);
        let s = incomingKeys.get(c);
        if (!s) incomingKeys.set(c, s = new Set());
        s.add(key);
        // A field of a value reached read-only from a crossing in at a
        // read-only type is a read-only position.
        const ro = t >= INCOMING_RO && !receiver.has(INCOMING + c);
        cross(f, at, c, "out", { field: { key } }, ro, tokens, at, ref);
      } else {
        const s = sites[t];
        if (s?.kind !== "array" || key === null || !/^\d+$/.test(key)) addKey(t, s?.kind === "array" && key === null ? "[]" : key);
        addAll(contentOf(t), tokens);
      }
    }
  };
  // Native calls read transitive storage only for a fresh result that can
  // hold references. Keep those reads and the one-hop reads as growing sets.
  type NativeFlow = { passed: FlowTokens; given: FlowTokens; all: FlowTokens; reached: FlowTokens; elements: FlowTokens };
  const nativeFlows = new Map<Node, NativeFlow>();
  const call = (n: Node, f: File): void => {
    if (!(ts.isCallExpression(n) || ts.isNewExpression(n))) return;
    const args = n.arguments ?? [];
    const { tokens, receiver } = calleeTokens(n.expression, f);
    const callee = unwrap(n.expression);
    const argRef = (a: Node): number => ts.isSpreadElement(a) ? exprRef(a.expression, f) : exprRef(a, f);
    const event: CallAst | null = recording ? { module: f.location, at: span(f, n), component: componentAt(n, f),
      callee: exprRef(n.expression, f),
      receiver: ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee) ? exprRef(callee.expression, f) : null,
      args: args.map((a, i) => ({ value: argRef(a), spread: ts.isSpreadElement(a), at: span(f, a),
        type: shapeOf(calleeParameterTypes(n.expression)[i], f) })), result: refNode(n), targets: [],
      instance: null, native: null, library: libraryCallsAt(n, args) } : null;
    const target = (c: Code | null): void => {
      const i = c === null ? -1 : codes.indexOf(c);
      if (event && i >= 0 && !event.targets.includes(i)) event.targets.push(i);
    };
    // A call TypeScript resolves to a member of the standard library's
    // arrays is that native's: a value at an array type is a built-in array,
    // holding the standard prototype and owning no key it declares (the
    // array invariant, DESIGN.md, "Trust surface"). So is one of another
    // interface's methods whose receiver is the family's own storage, no
    // record of which may have a key of that name: a collection's methods
    // are its prototype's, not what it holds.
    const otherMember = libraryMemberCalls.get(n);
    const libraryMember = arrayMemberCalls.has(n) || (otherMember !== undefined && receiver !== null &&
      incomingOf(receiver).length === 0 && sitesOf(receiver).every((t) => !mayHoldKey(t, otherMember)));
    let codeTargets = 0;
    let constructed: { index: number; node: Node } | undefined;
    for (const t of libraryMember ? [] : sitesOf(tokens)) {
      const s = sites[t];
      if (!s || !(functionLike(s.node) || classLike(s.node))) continue;
      codeTargets++;
      if (ts.isNewExpression(n) && classLike(s.node)) {
        const i = site(n, f, "instance");
        constructed = { index: i, node: s.node };
        addAll(storageOf(n), [i]);
        if (event) event.instance = i;
        for (let c: Node | undefined = s.node; c; c = baseOf(c, f)) {
          addAll(storageOf(instancesKey(c)), [i]);
          include(instancesKey(c), { site: i });
          const ctor = codeOf.get(constructorOf(c));
          if (ctor) addAll(storageOf(ctor.receiver), [i]);
          target(callCode(c, args, f, n, null));
        }
      } else target(callCode(s.node, args, f, n, receiver));
    }
    if (constructed && classOfInstance.get(constructed.index) !== constructed.node) {
      classOfInstance.set(constructed.index, constructed.node);
      worklist.grow(`instance:${constructed.index}`);
    }
    const outside = libraryMember ? [] : incomingOf(tokens);
    if (outside.length > 0) {
      const types = calleeParameterTypes(n.expression);
      for (const c of outside) {
        args.forEach((a, i) => cross(f, a, c, "out", { argument: { call: span(f, n), index: i } },
          readOnly(types[i], f), ts.isSpreadElement(a) ? reads(value(a.expression, f)) : value(a, f), a,
          event ? (ts.isSpreadElement(a) ? synthetic(a, f, [{ read: argRef(a) }]) : argRef(a)) : null));
        addAll(storageOf(n), [INCOMING + c]);
        cross(f, n, c, "in", { callResult: { call: span(f, n) } }, false, new Set([INCOMING + c]), null, event ? event.result : null);
      }
    }
    if (codeTargets === 0 && outside.length === 0) {
      if (!libraryMember && worklist.defer()) return;
      // A native: its result a site of its own, or its receiver, an argument
      // or what they hold; its receiver may hold its arguments; a closure it
      // is given may be called with any of these.
      const result = site(n, f, "native");
      // A member of the standard library's arrays whose reviewed contract
      // states a fresh result (`freshArrayMember`): the result is the array
      // it allocates, holding what the arguments pass and what is reachable
      // from the elements of what it is given and from its callbacks' results.
      const member = arrayMemberCalls.get(n);
      const fresh = member !== undefined && freshArrayMember(member);
      // Its elements, where TypeScript types it an array of primitives,
      // hold no reference.
      const primitiveElements = fresh && primitiveElementCalls.has(n);
      let flow = nativeFlows.get(n);
      if (!flow) nativeFlows.set(n, flow = { passed: new FlowTokens(), given: new FlowTokens(), all: new FlowTokens(),
        reached: new FlowTokens(), elements: new FlowTokens() });
      const { passed, given, all, reached, elements } = flow;
      for (const a of args) {
        if (ts.isSpreadElement(a)) readInto(passed, value(a.expression, f));
        else addAll(passed, value(a, f));
      }
      if (receiver) addAll(given, receiver);
      given.copyFrom(passed);
      all.add(result);
      all.copyFrom(given);
      readInto(all, given);
      const holdsReferences = fresh && !primitiveElements;
      if (holdsReferences) readInto(reached, given);
      const passedRef = event ? synthetic(n, f, event.args.map((a): SourceAst => a.spread ? { read: a.value } : { value: a.value })) : -1;
      const givenRef = event ? synthetic(n, f, [...(event.receiver !== null ? [{ value: event.receiver }] : []), { value: passedRef }]) : -1;
      const allFrom: SourceAst[] = [{ site: result }, { value: givenRef }, { read: givenRef }];
      // Its callbacks: each may be given what any of them returns, as
      // `reduce`'s accumulator is.
      const callbacks = args.flatMap((a) => sitesOf(value(a, f)).flatMap((t) => {
        const s = sites[t];
        const code = s && functionLike(s.node) ? codeOf.get(s.node) : undefined;
        return code ? [code] : [];
      }));
      for (const code of callbacks) {
        const returned = setOf(code.result);
        all.copyFrom(returned);
        if (holdsReferences) reached.copyFrom(returned);
        if (event) allFrom.push({ value: refOf(code.result) });
      }
      for (const code of callbacks) for (const p of code.params) bindParameter(p, all, code.file);
      for (const t of sitesOf(receiver ?? [])) {
        const s = sites[t];
        addAll(contentOf(t), passed);
        // A library method writes its receiver's elements or internal
        // slots, no key; any other native may add any.
        if (s && s.kind !== "array" && !libraryMember) addKey(t, null);
      }
      // Else its result may be any of these, and its own storage hold them.
      if (fresh) {
        addAll(storageOf(n), [result]);
        if (holdsReferences) {
          readInto(reached, reached);
          elements.copyFrom(passed);
          elements.copyFrom(reached);
          addAll(contentOf(result), elements);
        }
      } else {
        addAll(storageOf(n), all);
        addAll(contentOf(result), all);
      }
      if (event) event.native = { site: result, passed: passedRef, given: givenRef, all: synthetic(n, f, allFrom), member: libraryMember,
        name: arrayMemberCalls.get(n) ?? otherMember ?? null, array: arrayMemberCalls.has(n),
        fresh, primitiveElements };
    }
    if (event) events.calls.push(event);
  };

  /** **The suspensions** of a file's code: each `await` (a `for await`'s
   * among them), `yield`, async function and generator, at its innermost
   * component, nested and unused bodies included. */
  const suspensions: SuspensionAst[] = [];
  const collectSuspensions = (f: File): void => {
    const visit = (n: Node): void => {
      const at = (kind: SuspensionAst["kind"]): void => {
        suspensions.push({ module: f.location, at: span(f, n), component: componentAt(n, f), kind });
      };
      if (ts.isAwaitExpression(n) || (ts.isForOfStatement(n) && n.awaitModifier)) at("await");
      else if (ts.isYieldExpression(n)) at("yield");
      if (functionLike(n)) {
        const modifiers = ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n)
          ? n.modifiers : undefined;
        if (modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) at("async");
        if ((ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isMethodDeclaration(n)) && n.asteriskToken) at("generator");
      }
      n.forEachChild(visit);
    };
    visit(f.source);
  };

  // Bindings captured by another body can propagate marks and crossings.
  const holdsOf = (decl: Node): number | null => {
    const holder = holderOf(decl);
    const f = fileAt(decl);
    if (!holder || !f) return null;
    return ts.isSourceFile(holder) ? f.module : codeOf.get(holder)?.component ?? null;
  };
  const captured = new Set<Node>();
  for (const f of files) {
    const visit = (n: Node): void => {
      if (ts.isIdentifier(n) && reference(n)) {
        const decl = resolveName(n);
        if (decl) {
          const holder = holderOf(decl);
          const user = enclosingCode(n);
          if (holder && user && user.node !== holder && !ts.isSourceFile(holder)) captured.add(decl);
        }
      }
      n.forEachChild(visit);
    };
    visit(f.source);
  }
  for (let c = 0; c < components.length; c++) memberOf(c);
  // Entrypoints and escaped closures can be called from outside.
  const seedMember = (c: number, m: Node): void => {
    const code = codeOf.get(m);
    if (!code) return;
    code.params.forEach((p, i) => {
      const ro = readOnly(typeOfParameter(p), code.file);
      const token = (ro ? INCOMING_RO : INCOMING) + c;
      bindParameter(p, new Set([token]), code.file);
      cross(code.file, p, c, "in", { parameter: { code: span(code.file, code.node), index: i } },
        ro, new Set([token]), null, recording ? refNode(p) : null);
    });
    if (!ts.isArrowFunction(m)) addAll(storageOf(code.receiver), [INCOMING + c]);
    cross(code.file, code.node, c, "out", { result: { code: span(code.file, code.node) } },
      readOnly(resultType(code.node), code.file), setOf(code.result), null, recording ? refOf(code.result) : null);
  };
  for (const [c, ms] of members) for (const m of ms) worklist.add(() => seedMember(c, m));

  // Exported bindings cross out of their module and any package it enters.
  const exports: FlowRule[] = [];
  for (const f of files) for (const s of f.source.statements) {
    if (!ts.isVariableStatement(s) || !exported(s)) continue;
    for (const d of s.declarationList.declarations) for (const id of boundNames(d.name)) {
      if (!ts.isIdentifier(id)) continue;
      const outs = [f.module, ...(packageIndex !== null && entryModules.includes(f.absolute) ? [packageIndex] : [])];
      const emit = (): void => {
        const ref = recording ? refNode(id) : null;
        if (ref !== null) events.exports.push({ module: f.location, at: span(f, id), name: id.text, components: outs, value: ref,
          type: shapeOf(d.type, f) });
        for (const c of outs) cross(f, id, c, "out", { binding: { name: id.text } }, readOnly(d.type, f), setOf(id), id, ref);
      };
      exports.push(emit);
      worklist.add(emit);
    }
  }

  // Record the transfer rules in source order, for the final evidence pass.
  const statements: FlowRule[] = [];
  for (const f of files) {
    const compile = (n: Node): void => {
      const rule = compileTransfer(n, f);
      if (rule !== undefined) {
        statements.push(rule);
        worklist.add(rule);
      }
      n.forEachChild(compile);
    };
    compile(f.source);
  }

  // A module or a closure holds its own bindings and the bindings it captures.
  const holds: FlowRule[] = [];
  onBinding = (decl) => {
    const holder = holderOf(decl);
    const heldBy = holdsOf(decl);
    const f = fileAt(decl);
    if (!f || !holder || heldBy === null || !ts.isIdentifier(decl) || !(ts.isSourceFile(holder) || captured.has(decl))) return;
    let observed = 0;
    const hold = (): void => {
      const ref = recording ? refNode(decl) : null;
      if (ref !== null) events.holds.push({ module: f.location, at: span(f, decl), component: heldBy, name: decl.text, value: ref });
      const values = setOf(decl);
      for (const t of values.since(recording ? 0 : observed)) {
        const s = sites[t];
        if (!s) continue;
        for (const c of enclosing(s.component))
          if (!within(heldBy, c)) cross(f, decl, c, "out", { binding: { name: decl.text } }, false, new Set([t]), decl, ref);
          else if (!recording) raise(t, c, "internal");
      }
      observed = values.size;
    };
    holds.push(hold);
    if (!recording) worklist.add(hold);
  };

  // A mark flows to inner components and to storage the site can reach.
  // Exposing or releasing a closure also makes its code a component member.
  onSite = (t, s) => {
    const chain = enclosing(s.component);
    for (const [i, c] of chain.entries()) {
      let propagated: Mark = "local";
      let observed = 0;
      worklist.add(() => {
        const mark = markOf(t, c);
        if (mark === "local") return;
        if (mark !== propagated) {
          for (const d of chain.slice(0, i)) raise(t, d, mark);
          observed = 0;
          propagated = mark;
        }
        const contents = contentsNow(t);
        for (const u of contents.since(observed)) {
          const v = sites[u];
          if (v && within(v.component, c)) raise(u, c, mark);
        }
        observed = contents.size;
        if (functionLike(s.node) && rank(mark) >= rank("exposed") && !memberOf(c).has(s.node)) {
          memberOf(c).add(s.node);
          worklist.add(() => seedMember(c, s.node));
        }
      });
    }
  };
  sites.forEach((s, t) => onSite?.(t, s));

  worklist.solve(() => ruleValues.clear());
  onSite = undefined;
  // A record of a site exposed for a component may have every key a write of
  // that component's code adds to an incoming value.
  for (const [c, written] of incomingKeys)
    for (let t = 0; t < sites.length; t++)
      if (markOf(t, c) === "exposed") for (const k of written) addKey(t, k);
  // The record: one more round, the flow solved, stating each set's
  // inclusions and the events.
  recording = true;
  ruleValues.clear();
  for (const [c, ms] of members) for (const m of ms) seedMember(c, m);
  for (const emit of exports) emit();
  for (const rule of statements) rule();
  for (const hold of holds) hold();
  for (const c of codes) for (const p of c.params) if (ts.isParameterDeclaration(p)) refNode(p);
  for (const f of files) collectSuspensions(f);

  // The package's interface, by its entry modules' exports.
  const entryList = (c: number): EntryAst[] => [...entriesOf(c)].flatMap(([name, n]) => {
    const f = fileAt(n);
    return f ? [{ name, module: f.location, pos: span(f, n) }] : [];
  });
  for (let c = 0; c < components.length; c++) {
    const component = components[c];
    if (component && "known" in component.interface) component.interface = { known: { entries: entryList(c) } };
  }

  // The description.
  // Each site's contents, and each code's values, stated.
  const contentRefs = sites.map((_, t) => refOf(contentKey(t)));
  const codesList: ComponentsAst["codes"] = codes.map((c) => ({ module: c.file.location, pos: span(c.file, c.node),
    component: c.component, site: siteOf.get(c.node) ?? null,
    params: c.params.map((p) => ({ value: refNode(p), at: span(c.file, p), type: shapeOf(typeOfParameter(p), c.file) })),
    receiver: refOf(c.receiver), result: refOf(c.result), resultType: shapeOf(resultType(c.node), c.file),
    arrow: ts.isArrowFunction(c.node) }));
  const thrownRef = files.length > 0 ? refOf(thrownKey) : null;
  // Each value's tokens: a set's own; a computed one's, what it includes,
  // which are sets and computed values stated before it.
  const tokensOf: FlowValues[] = rows.map((r) => r.key !== null ? setOf(r.key) : new Set());
  const evaluate = (x: SourceAst): Iterable<number> =>
    "site" in x ? [x.site] : "incoming" in x ? [INCOMING + x.incoming] : "incomingReadOnly" in x ? [INCOMING_RO + x.incomingReadOnly]
      : "value" in x ? tokensOf[x.value] ?? []
      : reads(tokensOf[x.read] ?? new Set());
  rows.forEach((r, i) => {
    if (r.key === null) tokensOf[i] = new Set(r.from.flatMap((x) => [...evaluate(x)]));
  });
  const values: ComponentsAst["values"] = rows.map((r, i) => {
    const tokens = tokensOf[i] ?? new Set<number>();
    return { module: r.module, pos: r.pos, sites: sitesOf(tokens).sort((a, b) => a - b),
      incoming: writableIncoming(tokens).sort((a, b) => a - b), incomingReadOnly: readOnlyIncoming(tokens).sort((a, b) => a - b),
      from: r.from };
  });
  const crossingList: CrossingAst[] = [...crossings.values()].map((x) => ({ module: x.module, at: x.at, component: x.component,
    direction: x.direction, position: x.position, readOnly: x.readOnly, value: x.value }));
  const escapes: ComponentsAst["escapes"] = [];
  const escaped = new Set<string>();
  for (const x of crossings.values()) {
    if (x.direction !== "out" || x.via === null) continue;
    const seen = new Set<number>();
    const work = sitesOf(x.tokens);
    for (let t = work.pop(); t !== undefined; t = work.pop()) {
      if (seen.has(t)) continue;
      seen.add(t);
      const s = sites[t];
      if (!s) continue;
      const key = `${t}:${x.component}:${x.via}:${x.at.join(":")}`;
      if (functionLike(s.node) && within(s.component, x.component) && !escaped.has(key)) {
        escaped.add(key);
        escapes.push({ module: s.file.location, code: span(s.file, s.node), component: x.component, via: x.via, at: x.at });
      }
      work.push(...sitesOf(contentsNow(t)));
    }
  }
  const clients = files.flatMap((f) => f.source.statements.flatMap((s) => {
    if (!(ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s)) || !exported(s)) return [];
    const tags = clientsTags(leading(f.source, s));
    if (tags.length > 1) return input.fail(f.absolute === resolve(input.absolute) ? s : null, `${s.name.text} states more than one \`@clients\``);
    const [tag] = tags;
    if (tag !== undefined && packageIndex !== null) {
      const p = components[packageIndex];
      if (p && "unknown" in p.interface)
        return input.fail(f.absolute === resolve(input.absolute) ? s : null,
          `\`@clients\` on ${s.name.text} states the row of a component whose interface is unknown: ${p.interface.unknown.reason}` +
          (f.absolute === resolve(input.absolute) ? "" : ` (in ${f.location})`));
    }
    const frame = tag === undefined ? [] : clientsFrame(tag, (message) =>
      input.fail(f.absolute === resolve(input.absolute) ? s : null, `\`@clients\` on ${s.name.text}: ${message}` + (f.absolute === resolve(input.absolute) ? "" : ` (in ${f.location})`)));
    return [{ module: f.location, name: s.name.text, pos: span(f, s), stated: tag !== undefined, frame }];
  }));
  const siteList: SiteAst[] = sites.map((s, t) => ({ module: s.file.location, pos: span(s.file, s.node), kind: s.kind,
    keys: [...(keys.get(t) ?? [])].sort(), anyKey: anyKey.has(t), contents: contentRefs[t] ?? 0,
    marks: enclosing(s.component).map((c) => ({ component: c, mark: markOf(t, c) })) }));
  const described: ComponentsAst = { components, codes: codesList, sites: siteList, values, crossings: crossingList, ...events,
    thrown: thrownRef, suspensions, types: typeRows, escapes, clients, guarantees: input.guarantees(), protocols: [],
    frameParts: [], frameEntries: [], frames: [] };
  return { ...described, protocols: proposeProtocols(described), ...proposeFrames(described) };
}

/** **Each component's proposed protocol** `Ψ_C` (the draft, "The
 * protocol"): the join, part by part, of the charges of every write of its
 * code, as `ComponentChecks.protocolDiags` checks them. A write charges
 * nothing where it is an initial value of the record it allocates or its
 * receiver is fresh at the write (every location it may hold allocated by
 * the write's frame or, through closures confined to their frames, by an
 * enclosing frame, `Ctx.freshScope`); else each part it changes at each storage of the
 * component's region it may write: its receiver's exposed and released
 * sites and, where the receiver may enter from outside, every exposed and
 * released site and outside storage. A field or a cell changes by `any`; an
 * element's write lengthens a spine (`grow`), a write of no value or of
 * `length` changes it by `any`; a native changes its receiver's spine,
 * cells and fields by `any`, the reviewed contracts stating no effect at a
 * throw. */
export function proposeProtocols(F: ComponentsAst): ComponentsAst["protocols"] {
  const codeMemo = new Map<string, number | null>();
  const codeAt = (module: string, at: Span): number | null => {
    const id = `${module}\u0000${at[0]}\u0000${at[1]}`;
    const known = codeMemo.get(id);
    if (known !== undefined) return known;
    let best: number | null = null;
    let width = Infinity;
    F.codes.forEach((c, i) => {
      if (c.module === module && c.pos[0] <= at[0] && at[1] <= c.pos[1] && c.pos[1] - c.pos[0] < width) {
        best = i;
        width = c.pos[1] - c.pos[0];
      }
    });
    codeMemo.set(id, best);
    return best;
  };
  const boundary = new Set<number>([...F.codes.flatMap((c) => [c.receiver, c.result, ...c.params.map((p) => p.value)]),
    ...F.catches.map((k) => k.value)]);
  const resultOf = new Map<number, CallAst>();
  for (const c of F.calls) if (!resultOf.has(c.result)) resultOf.set(c.result, c);
  const valueOf = (v: number): ValueAst | undefined => F.values[v];
  const contentsOf = (t: number): ValueAst | undefined => { const s = F.sites[t]; return s === undefined ? undefined : valueOf(s.contents); };
  const codeAtSite = new Map<number, number>();
  F.codes.forEach((c, i) => { if (c.site !== null) codeAtSite.set(c.site, i); });
  const calleeOutside = (c: CallAst): boolean => {
    if (c.native?.member ?? false) return false;
    const x = valueOf(c.callee);
    return x !== undefined && (x.incoming.length > 0 || x.incomingReadOnly.length > 0);
  };
  const parentCode = (k: number): number | null => {
    const c = F.codes[k];
    if (!c) return null;
    let best: number | null = null;
    let width = Infinity;
    F.codes.forEach((d, i) => {
      if (i !== k && d.module === c.module && d.pos[0] <= c.pos[0] && c.pos[1] <= d.pos[1] && d.pos[1] - d.pos[0] < width) {
        best = i;
        width = d.pos[1] - d.pos[0];
      }
    });
    return best;
  };
  // A closure confined to the frames that hold it, as `Ctx.confined`.
  // The sites some storage, code result, throw, held or exported binding,
  // stored value, native or outside callee may hold or be given.
  const escaping = new Set<number>();
  const escape = (v: number | null): void => { if (v !== null) for (const t of valueOf(v)?.sites ?? []) escaping.add(t); };
  for (const site of F.sites) escape(site.contents);
  for (const c of F.codes) escape(c.result);
  escape(F.thrown);
  for (const p of [...F.throws, ...F.holds]) escape(p.value);
  for (const e of F.exports) escape(e.value);
  for (const st of F.stores) escape(st.stored);
  for (const c of F.calls) if (c.native !== null || calleeOutside(c)) {
    escape(c.receiver);
    for (const a of c.args) escape(a.value);
  }
  const confined = (k: number): boolean => {
    const s = F.codes[k]?.site ?? null;
    return s !== null && !escaping.has(s) && (F.sites[s]?.marks.every((m) => m.mark === "local" || m.mark === "internal") ?? false);
  };
  const freshIn = (scope: readonly number[], v: number, fuel: number): boolean => {
    const x = F.values[v];
    if (fuel === 0 || x === undefined) return false;
    const inScope = (k: number | null): boolean => k !== null && scope.includes(k);
    const siteIn = (t: number): boolean => { const s = F.sites[t]; return s !== undefined && inScope(codeAt(s.module, s.pos)); };
    if (x.incoming.length > 0 || x.incomingReadOnly.length > 0 || boundary.has(v) || !inScope(codeAt(x.module, x.pos)) ||
      !x.sites.every(siteIn)) return false;
    const call = resultOf.get(v);
    if (call !== undefined) return inScope(codeAt(call.module, call.at)) && call.native !== null && call.native.member &&
      call.native.array && call.native.fresh;
    return x.from.length > 0 && x.from.every((s) => "site" in s ? siteIn(s.site) : "value" in s ? freshIn(scope, s.value, fuel - 1) : false);
  };
  // Fresh at a place, as `Ctx.freshAt`.
  const freshAt = (module: string, at: Span, v: number): boolean => {
    const k = codeAt(module, at);
    if (k === null) return false;
    const fuel = F.values.length + 1;
    let scope = [k];
    for (let cur: number | null = k, n = 0; cur !== null && n <= F.codes.length; n++) {
      if (freshIn(scope, v, fuel)) return true;
      if (!confined(cur)) return false;
      cur = parentCode(cur);
      if (cur !== null) scope = [cur, ...scope];
    }
    return false;
  };
  const chain = (c: number): number[] => {
    const out: number[] = [];
    for (let d: number | null | undefined = c; d !== null && d !== undefined && out.length <= F.components.length; d = F.components[d]?.parent)
      out.push(d);
    return out;
  };
  const markOf = (t: number, C: number): Mark | null => F.sites[t]?.marks.find((m) => m.component === C)?.mark ?? null;
  const lent = (t: number, C: number): boolean => { const m = markOf(t, C); return m === "exposed" || m === "released"; };
  const targets = (C: number, v: number): (number | null)[] => {
    const x = F.values[v];
    if (!x) return [];
    const own = x.sites.filter((t) => lent(t, C));
    const enters = x.incoming.includes(C) || x.incomingReadOnly.includes(C);
    return enters ? [...own, ...F.sites.flatMap((_, t) => lent(t, C) ? [t] : []), null] : own;
  };
  type Part = Omit<ProtocolEntryAst, "site">;
  const storeParts = (kind: SiteAst["kind"] | null, key: string | null, element: boolean, valued: boolean): Part[] => {
    const numeric = key !== null && /^\d+$/.test(key);
    const arr: Part[] = element || numeric
      ? [{ kind: "cell", key: null, change: "any" }, { kind: "spine", key: null, change: valued ? "grow" : "any" }]
      : key === "length" ? [{ kind: "spine", key: null, change: "any" }]
      : key !== null ? [{ kind: "field", key, change: "any" }]
      : [{ kind: "cell", key: null, change: "any" }, { kind: "spine", key: null, change: "any" }, { kind: "field", key: null, change: "any" }];
    const rec: Part[] = [{ kind: "field", key: element ? null : key, change: "any" }];
    return kind === "array" ? arr : kind === "native" || kind === null ? [...arr, ...rec] : rec;
  };
  const nativeParts: Part[] = [{ kind: "spine", key: null, change: "any" }, { kind: "cell", key: null, change: "any" },
    { kind: "field", key: null, change: "any" }];
  type Write = { component: number; module: string; at: Span; receiver: number; parts: (k: SiteAst["kind"] | null) => Part[]; initial: boolean };
  const writes: Write[] = [
    ...F.stores.map((s): Write => ({ component: s.component, module: s.module, at: s.at, receiver: s.receiver,
      parts: (k) => storeParts(k, s.key, s.element, s.stored !== null), initial: s.initial })),
    ...F.calls.flatMap((c): Write[] => c.native !== null && c.receiver !== null
      ? [{ component: c.component, module: c.module, at: c.at, receiver: c.receiver, parts: () => nativeParts, initial: false }] : []),
  ];
  const rank: Record<Change, number> = { keep: 0, init: 1, scalar: 2, extend: 3, grow: 4, any: 5 };
  const byComponent = new Map<number, Map<string, ProtocolEntryAst>>();
  for (const w of writes) {
    if (w.initial || freshAt(w.module, w.at, w.receiver)) continue;
    for (const C of chain(w.component)) {
      let entries = byComponent.get(C);
      if (!entries) byComponent.set(C, entries = new Map());
      for (const site of targets(C, w.receiver)) {
        for (const p of w.parts(site === null ? null : F.sites[site]?.kind ?? null)) {
          const id = JSON.stringify([site, p.kind, p.key]);
          const known = entries.get(id);
          if (!known || rank[known.change] < rank[p.change]) entries.set(id, { site, ...p });
        }
      }
    }
  }
  return [...byComponent].sort(([a], [b]) => a - b).map(([component, entries]) => ({ component, entries: [...entries.values()] }));
}

/** **The proposed frame at each call of code outside a component**
 * (Read-only frames, Proposition "Read-only reliance", its premise location
 * by location), as `ComponentChecks.Ctx.frames` checks it: at each call that
 * may run code outside a component it lies in, for each parameter of the
 * innermost code holding the call, each field of its records (`h.widths`),
 * and each site that code allocates, the regions of its storage (a record's
 * fields at every key, an array's spine and cells), with the parts their locations may have for each such
 * component (`Ctx.frameParts`) and whether they are protected for every one
 * (`Ctx.frameProtected`). */
export function proposeFrames(F: ComponentsAst): Pick<ComponentsAst, "frameParts" | "frameEntries" | "frames"> {
  const chain = (c: number): number[] => {
    const out: number[] = [];
    for (let d: number | null | undefined = c; d !== null && d !== undefined && out.length <= F.components.length; d = F.components[d]?.parent)
      out.push(d);
    return out;
  };
  const markOf = (t: number, C: number): Mark | null => F.sites[t]?.marks.find((m) => m.component === C)?.mark ?? null;
  const innermost = (module: string, at: Span): number | null => {
    let best: number | null = null;
    let width = Infinity;
    F.codes.forEach((c, i) => {
      if (c.module === module && c.pos[0] <= at[0] && at[1] <= c.pos[1] && c.pos[1] - c.pos[0] < width) {
        best = i;
        width = c.pos[1] - c.pos[0];
      }
    });
    return best;
  };
  type Tokens = { sites: readonly number[]; incoming: readonly number[]; ro: readonly number[] };
  const contentsOf = (t: number): Tokens => {
    const x = F.values[F.sites[t]?.contents ?? -1];
    return x ? { sites: x.sites, incoming: x.incoming, ro: x.incomingReadOnly } : { sites: [], incoming: [], ro: [] };
  };
  // What storage of `T` holds (`ComponentChecks.Ctx.readTokens`).
  const readOf = (T: Tokens): Tokens => ({
    sites: T.sites.flatMap((t) => contentsOf(t).sites),
    incoming: [...T.incoming, ...T.sites.flatMap((t) => contentsOf(t).incoming)],
    ro: [...T.ro, ...T.sites.flatMap((t) => contentsOf(t).ro)],
  });
  const tokensOf = (root: FrameEntryAst["root"]): Tokens => {
    if ("site" in root) return { sites: [root.site], incoming: [], ro: [] };
    const x = F.values[root.value];
    const start: Tokens = x ? { sites: x.sites, incoming: x.incoming, ro: x.incomingReadOnly } : { sites: [], incoming: [], ro: [] };
    return root.fields.reduce((T) => readOf(T), start);
  };
  // The sites a value may be for `C`: its own, and every exposed and
  // released site of `C` where it may enter from outside (`partsFor`).
  const lentByComponent = F.components.map((): number[] => []);
  F.sites.forEach((s, t) => {
    for (const m of s.marks) if (m.mark === "exposed" || m.mark === "released") lentByComponent[m.component]?.push(t);
  });
  const lentOf = (C: number): number[] => lentByComponent[C] ?? [];
  // The fields of the records a value may be for the components `comps`.
  const fieldsOf = (v: number, comps: number[]): string[] => {
    const x = F.values[v];
    if (!x) return [];
    const sites = [...x.sites, ...comps.flatMap((C) => x.incoming.includes(C) || x.incomingReadOnly.includes(C) ? lentOf(C) : [])];
    return [...new Set(sites.flatMap((t) => {
      const s = F.sites[t];
      return s && (s.kind === "object" || s.kind === "instance") ? s.keys : [];
    }))];
  };
  const partsFor = (C: number, T: Tokens): (number | null)[] => {
    const own = T.sites.map((t) => markOf(t, C) !== null ? t : null);
    if (!(T.incoming.includes(C) || T.ro.includes(C))) return own;
    return [...own, ...lentOf(C), null];
  };
  const protectedFor = (C: number, T: Tokens): boolean => !T.incoming.includes(C) &&
    T.sites.every((t) => { const m = markOf(t, C); return m === "local" || m === "internal" || m === "exposed"; });
  const frameParts: ComponentsAst["frameParts"] = [];
  const partIds = new Map<string, number>();
  const partId = (parts: (number | null)[]): number => {
    const key = JSON.stringify(parts);
    const known = partIds.get(key);
    if (known !== undefined) return known;
    const id = frameParts.length;
    frameParts.push(parts);
    partIds.set(key, id);
    return id;
  };
  const every: FrameEntryAst["kind"][] = ["field", "spine", "cell"];
  type Root = { root: FrameEntryAst["root"]; kinds: FrameEntryAst["kind"][] };
  const sitesByCode = new Map<number, Root[]>();
  F.sites.forEach((s, t) => {
    if (s.kind !== "object" && s.kind !== "array" && s.kind !== "instance") return;
    const k = innermost(s.module, s.pos);
    if (k === null) return;
    const roots = sitesByCode.get(k) ?? [];
    roots.push({ root: { site: t }, kinds: s.kind === "array" ? ["spine", "cell"] : ["field"] });
    sitesByCode.set(k, roots);
  });
  const frameEntries: ComponentsAst["frameEntries"] = [];
  const templates = new Map<string, number | null>();
  // Calls in the same code with the same outside components propose the same frame.
  const templateFor = (k: number, comps: number[]): number | null => {
    const key = JSON.stringify([k, comps]);
    const known = templates.get(key);
    if (known !== undefined) return known;
    const code = F.codes[k];
    if (!code) return null;
    const roots: Root[] = [
      ...code.params.flatMap((p) => [{ root: { value: p.value, fields: [] }, kinds: every },
        ...(p.type === "function" || p.type === "primitive" ? [] : fieldsOf(p.value, comps)).map((f) => ({ root: { value: p.value, fields: [f] }, kinds: every }))]),
      ...(sitesByCode.get(k) ?? []),
    ];
    const entries: FrameEntryAst[] = roots.flatMap(({ root, kinds }) => {
      const T = tokensOf(root);
      if (T.sites.length === 0 && T.incoming.length === 0 && T.ro.length === 0) return [];
      const parts = partId([...new Set(comps.flatMap((C) => partsFor(C, T)))]);
      const prot = comps.every((C) => protectedFor(C, T));
      return kinds.map((kind) => ({ root, kind, key: null, parts, protected: prot }));
    });
    const template = entries.length === 0 ? null : frameEntries.push(entries) - 1;
    templates.set(key, template);
    return template;
  };
  const frames: ComponentsAst["frames"] = [];
  F.calls.forEach((c, call) => {
    if (c.native?.member ?? false) return;
    const callee = F.values[c.callee];
    if (!callee) return;
    const comps = chain(c.component).filter((C) => callee.incoming.includes(C) || callee.incomingReadOnly.includes(C));
    if (comps.length === 0) return;
    const k = innermost(c.module, c.at);
    if (k === null) return;
    const entries = templateFor(k, comps);
    if (entries !== null) frames.push({ call, entries });
  });
  return { frameParts, frameEntries, frames };
}

const valuesClass: Selector = { value: true, array: false, view: false };
const arraysClass: Selector = { value: false, array: true, view: false };
const viewsClass: Selector = { value: false, array: false, view: true };
const CHANGES: readonly Change[] = ["keep", "init", "scalar", "extend", "grow", "any"];
const changeOf = (text: string): Change | null => CHANGES.find((c) => c === text) ?? null;

/** **A client obligation's frame** (`@clients P`): `P` a protocol of
 * `Modifies` (SOURCE-ELABORATION.md, "Stated effects") written as a type
 * literal, `values` and `spines` at a change, and quoted path keys rooted at
 * `this`, the value at the type: `"this.f"` a field, `"this.f.*"` the fields
 * of the value at `this.f`, `"this.f[*]"` the spine of the array there, each
 * at a change. An omitted class key is `keep`; `{}` is read-only. Refused:
 * any other key, `integrity` among them, which the model does not state. */
export function clientsFrame(text: string, fail: (message: string) => never): Frame {
  const body = text.trim();
  if (!body.startsWith("{") || !body.endsWith("}")) return fail(`a protocol is a type literal \`{ … }\`: ${body}`);
  const inner = body.slice(1, -1).trim();
  const frame: { region: Region; change: Change }[] = [];
  const seen = new Set<string>();
  const entries = inner === "" ? [] : inner.split(/[;,]/).map((p) => p.trim()).filter((p) => p !== "");
  for (const entry of entries) {
    const m = /^("([^"]*)"|([A-Za-z_$][\w$]*))\s*:\s*"([a-z]+)"$/.exec(entry);
    if (!m) return fail(`an entry is \`key: "change"\`: ${entry}`);
    const key = m[2] ?? m[3] ?? "";
    const change = changeOf(m[4] ?? "");
    if (change === null) return fail(`a change is one of ${CHANGES.join(", ")}: ${entry}`);
    if (seen.has(key)) return fail(`the key ${key} is stated twice`);
    seen.add(key);
    if (m[3] !== undefined && key === "values")
      frame.push({ region: { cls: valuesClass }, change: change === "extend" || change === "grow" ? "scalar" : change });
    else if (m[3] !== undefined && key === "spines") {
      const spine: Change = change === "init" || change === "scalar" ? "keep" : change;
      frame.push({ region: { cls: arraysClass }, change: spine }, { region: { cls: viewsClass }, change: spine });
    } else if (m[2] !== undefined) {
      const path = /^this((?:\.[A-Za-z_$][\w$]*)*)(\.\*|\[\*\])?$/.exec(key);
      const fields = (path?.[1] ?? "").split(".").filter((s) => s !== "");
      if (!path || (fields.length === 0 && path[2] === undefined))
        return fail(`a path key is rooted at \`this\`: \`"this.f"\`, \`"this.f.*"\` or \`"this.f[*]"\`, not ${key}`);
      if (path[2] === "[*]") frame.push({ region: { spine: { x: 0, fields } }, change });
      else if (path[2] === ".*") frame.push({ region: { pathFields: { x: 0, fields } }, change });
      else {
        const last = fields.at(-1) ?? "";
        const prefix = fields.slice(0, -1);
        frame.push({ region: prefix.length === 0 ? { field: { x: 0, key: last } } : { path: { x: 0, fields: prefix, key: last } }, change });
      }
    } else return fail(`\`${key}\` is no key of a client obligation: the keys are \`values\`, \`spines\` and quoted paths from \`this\``);
  }
  return frame;
}
