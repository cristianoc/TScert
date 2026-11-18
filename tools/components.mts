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
 * may also be its receiver, an argument or their contents. Marks are the
 * least the crossings, the holds by bindings and the stores allow. */
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile, TypeNode } from "typescript/unstable/ast";
import { dirname, join, relative, resolve, sep } from "node:path";
import { listDirectory, orAbsent, present, readText, realPath } from "./files.mts";
import { clientsTags, representationTags } from "./bound-annotations.mts";
import type { Change, Frame, Region, Selector } from "./declaration-types.mts";
import type { ComponentAst, ComponentsAst, CrossingAst, EntryAst, Mark, PositionAst, SiteAst } from "./fragment.mts";
import type { Json } from "./calculus.mts";
import type { Span } from "./span.mts";

/** A program the family is read from: its files by absolute path, each
 * one's tree, and whether TypeScript's type of each node is primitive, so
 * that no value of it holds a reference. */
export type FamilyProgram = {
  files: readonly string[];
  sourceOf: (absolute: string) => SourceFile | null;
  primitive: (nodes: readonly Node[]) => boolean[];
};

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

/** The empty description: no component. */
export const noComponents: ComponentsAst = { components: [], codes: [], sites: [], values: [], crossings: [],
  escapes: [], clients: [], guarantees: [] };

/** A build configuration: where it writes its outputs, the directory of
 * the sources they mirror, and the files it compiles. */
export type BuildConfig = { outDir: string | null; rootDir: string | null; fileNames: readonly string[] };
type Build = { outDir: string; rootDir: string; fileNames: readonly string[] };

type File = { absolute: string; location: string; source: SourceFile; module: number };
type Code = { node: Node; file: File; component: number; params: Node[]; result: Node; receiver: Node };
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
 * from outside by `INCOMING` plus its index. */
const INCOMING = 1 << 24;
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
  const enclosing = (c: number): number[] => {
    const out: number[] = [];
    for (let at: number | null = c; at !== null; at = components[at]?.parent ?? null) out.push(at);
    return out;
  };
  const within = (inner: number, outer: number): boolean => enclosing(inner).includes(outer);

  // Codes and sites.
  const codes: Code[] = [];
  const codeOf = new Map<Node, Code>();
  const sites: Site[] = [];
  const siteOf = new Map<Node, number>();
  const fileOfNode = new Map<Node, File>();
  const site = (node: Node, f: File, kind: SiteAst["kind"]): number => {
    const known = siteOf.get(node);
    if (known !== undefined) return known;
    const index = sites.length;
    sites.push({ node, file: f, kind, component: innermost(node, f) });
    siteOf.set(node, index);
    return index;
  };
  for (const f of files) {
    fileOfNode.set(f.source, f);
    const visit = (n: Node): void => {
      if (functionLike(n)) {
        const code: Code = { node: n, file: f, component: innermost(n, f), params: [...parametersOf(n)], result: n, receiver: n };
        codes.push(code);
        codeOf.set(n, code);
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

  // The reads and calls whose type is primitive hold no reference.
  const primitiveNodes = new Set<Node>();
  for (const f of files) {
    const asked: Node[] = [];
    const visit = (n: Node): void => {
      if (ts.isCallExpression(n) || ts.isPropertyAccessExpression(n) || ts.isElementAccessExpression(n)) asked.push(n);
      n.forEachChild(visit);
    };
    visit(f.source);
    reading.primitive(asked).forEach((p, i) => {
      const n = asked[i];
      if (p && n) primitiveNodes.add(n);
    });
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
  const sets = new Map<Node, Set<number>>();
  const contents = new Map<number, Set<number>>();
  let changed = true;
  const setOf = (key: Node): Set<number> => {
    let s = sets.get(key);
    if (!s) sets.set(key, s = new Set());
    return s;
  };
  const contentOf = (i: number): Set<number> => {
    let s = contents.get(i);
    if (!s) contents.set(i, s = new Set());
    return s;
  };
  const addAll = (into: Set<number>, from: Iterable<number>): void => {
    for (const t of from) if (!into.has(t)) { into.add(t); changed = true; }
  };
  const keys = new Map<number, Set<string>>();
  const anyKey = new Set<number>();
  const addKey = (i: number, key: string | null): void => {
    if (key === null) {
      if (!anyKey.has(i)) { anyKey.add(i); changed = true; }
      return;
    }
    let s = keys.get(i);
    if (!s) keys.set(i, s = new Set());
    if (!s.has(key)) { s.add(key); changed = true; }
  };
  const incomingKeys = new Map<number, Set<string | null>>();
  const outsideTokens = (): number[] => components.map((_, c) => INCOMING + c);
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
  const markOf = (s: number, c: number): Mark => marks.get(`${s}:${c}`) ?? "local";
  const raise = (s: number, c: number, m: Mark): boolean => {
    if (rank(markOf(s, c)) >= rank(m)) return false;
    marks.set(`${s}:${c}`, m);
    changed = true;
    return true;
  };

  // Read-only types, read from the syntax: primitives and literals, `unknown`,
  // read-only arrays and tuples of such types, records whose every member is a
  // readonly field of such a type, unions and intersections of such types, a
  // sealed handle, and a named type of the family whose definition is one.
  const roCache = new Map<Node, boolean>();
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
  const readOnly = (t: Node | undefined, f: File, depth: number = 0): boolean => {
    if (t === undefined || depth > 24) return false;
    const known = roCache.get(t);
    if (known !== undefined) return known;
    roCache.set(t, false);
    let ro = false;
    const k = t.kind;
    if (k === ts.SyntaxKind.NumberKeyword || k === ts.SyntaxKind.StringKeyword || k === ts.SyntaxKind.BooleanKeyword ||
        k === ts.SyntaxKind.BigIntKeyword || k === ts.SyntaxKind.SymbolKeyword || k === ts.SyntaxKind.UndefinedKeyword ||
        k === ts.SyntaxKind.VoidKeyword || k === ts.SyntaxKind.NeverKeyword || k === ts.SyntaxKind.UnknownKeyword ||
        ts.isLiteralTypeNode(t) || ts.isTemplateLiteralTypeNode(t)) ro = true;
    else if (ts.isParenthesizedTypeNode(t)) ro = readOnly(t.type, f, depth + 1);
    else if (ts.isTypeOperatorNode(t) && t.operator === ts.SyntaxKind.ReadonlyKeyword) {
      const inner = t.type;
      ro = ts.isArrayTypeNode(inner) ? readOnly(inner.elementType, f, depth + 1)
        : ts.isTupleTypeNode(inner) ? inner.elements.every((e) => readOnly(ts.isNamedTupleMember(e) ? e.type : e, f, depth + 1)) : false;
    } else if (ts.isUnionTypeNode(t) || ts.isIntersectionTypeNode(t)) ro = t.types.every((p) => readOnly(p, f, depth + 1));
    else if (ts.isTypeLiteralNode(t)) ro = t.members.every((m) => readOnlyMember(m, f, depth));
    else if (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName)) {
      const name = t.typeName.text, args = t.typeArguments ?? [];
      if (name === "ReadonlyArray" && args.length === 1) ro = readOnly(args[0], f, depth + 1);
      else if (args.length === 0) {
        const d = typeDecl(f, name);
        if (d !== null) {
          const trivia = leading(d.file.source, d.node);
          ro = representationTags(trivia).length > 0 ||
            (ts.isTypeAliasDeclaration(d.node) && readOnly(d.node.type, d.file, depth + 1)) ||
            (ts.isInterfaceDeclaration(d.node) && !d.node.heritageClauses?.length &&
              d.node.members.every((m) => readOnlyMember(m, d.file, depth)));
        }
      }
    }
    roCache.set(t, ro);
    return ro;
  };
  const readOnlyMember = (m: Node, f: File, depth: number): boolean =>
    ts.isPropertySignatureDeclaration(m) ? !!m.modifiers?.some((x) => x.kind === ts.SyntaxKind.ReadonlyKeyword) &&
      readOnly(m.type, f, depth + 1)
    : ts.isIndexSignatureDeclaration(m) ? !!m.modifiers?.some((x) => x.kind === ts.SyntaxKind.ReadonlyKeyword) &&
      readOnly(m.type, f, depth + 1) : false;
  const typeOfParameter = (p: Node | undefined): TypeNode | undefined => p && ts.isParameterDeclaration(p) ? p.type : undefined;
  const resultType = (n: Node): TypeNode | undefined =>
    ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
    ts.isGetAccessorDeclaration(n) ? n.type : undefined;

  // Crossings, collected by the last round.
  const crossings = new Map<string, CrossingAst & { tokens: Set<number>; node: Node | null; via: "result" | "argument" | "throw" | "store" | null }>();
  const cross = (f: File, at: Node, c: number, direction: "in" | "out", position: PositionAst, ro: boolean,
      tokens: Set<number> | null, valueNode: Node | null): void => {
    const key = `${f.absolute}:${at.getStart(f.source)}:${at.end}:${c}:${direction}:${JSON.stringify(position)}`;
    const via = direction === "in" ? null : typeof position === "object" && "result" in position ? "result"
      : typeof position === "object" && "argument" in position ? "argument" : position === "thrown" ? "throw" : "store";
    const held = crossings.get(key);
    if (held) {
      if (tokens) addAll(held.tokens, tokens);
      return;
    }
    crossings.set(key, { module: f.location, at: span(f, at), component: c, direction, position, readOnly: ro, value: null,
      tokens: new Set(tokens ?? []), node: valueNode, via });
    changed = true;
  };

  const thrown = new Set<number>();
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
  const incomingOf = (tokens: Iterable<number>): number[] => [...tokens].filter((t) => t >= INCOMING).map((t) => t - INCOMING);
  const sitesOf = (tokens: Iterable<number>): number[] => [...tokens].filter((t) => t < INCOMING);
  const reads = (tokens: Set<number>): Set<number> => {
    const out = new Set<number>();
    for (const t of tokens) {
      if (t >= INCOMING) out.add(t);
      else for (const x of contents.get(t) ?? []) out.add(x);
    }
    return out;
  };

  /** The tokens of an expression's value. */
  // An expression's value is computed once a round.
  let roundValues = new Map<Node, Set<number>>();
  const value = (e: Node | undefined, f: File): Set<number> => {
    if (e === undefined) return new Set();
    const held = roundValues.get(e);
    if (held) return held;
    const computed = valueNow(e, f);
    roundValues.set(e, computed);
    return computed;
  };
  const valueNow = (e: Node, f: File): Set<number> => {
    const x = unwrap(e);
    if (primitiveNodes.has(x)) return new Set();
    if (ts.isIdentifier(x)) return identifierValue(x, f);
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
  const identifierValue = (id: Node, f: File): Set<number> => {
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

  /** Bind a binding name to tokens: each name the whole value, or what a
   * pattern reads of it. */
  const bind = (name: Node, tokens: Set<number>, f: File): void => {
    if (ts.isIdentifier(name)) addAll(setOf(name), tokens);
    else if (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name))
      for (const e of name.elements) if (ts.isBindingElement(e)) {
        const read = e.dotDotDotToken ? new Set([...reads(tokens), site(e, f, ts.isArrayBindingPattern(name) ? "array" : "object")]) : reads(tokens);
        if (e.dotDotDotToken) addAll(contentOf(site(e, f, "object")), reads(tokens));
        if (e.name) bind(e.name, new Set([...read, ...value(e.initializer, f)]), f);
      }
  };
  /** The tokens a call's callee may be: the closures it may run, and the
   * components it may enter from outside. */
  const calleeTokens = (callee: Node, f: File): { tokens: Set<number>; receiver: Set<number> | null } => {
    const x = unwrap(callee);
    if (ts.isPropertyAccessExpression(x) || ts.isElementAccessExpression(x)) {
      const receiver = value(x.expression, f);
      const tokens = reads(receiver);
      const name = ts.isPropertyAccessExpression(x) ? x.name.text : nameText(x.argumentExpression);
      // A method of a class whose instance the receiver may be, or of the
      // class itself where the receiver is a class value.
      for (const t of sitesOf(receiver)) {
        const s = sites[t];
        if (!s) continue;
        const cls = s.kind === "instance" ? classOfInstance.get(t) : classLike(s.node) ? s.node : undefined;
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
  const callCode = (target: Node, args: readonly Node[], f: File, call: Node, receiver: Set<number> | null): void => {
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
      if (receiver) addAll(setOf(c.receiver), receiver);
      if (!classLike(target)) addAll(setOf(call), setOf(c.result));
    }
  };
  const bindParameter = (p: Node, tokens: Set<number>, f: File): void => {
    if (!ts.isParameterDeclaration(p)) return;
    addAll(setOf(p), tokens);
    bind(p.name, p.dotDotDotToken ? new Set([...tokens]) : tokens, f);
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

  /** One round over a file's code: every inclusion its statements and
   * expressions state, the crossings among them. */
  const walk = (f: File): void => {
    const visit = (n: Node): void => {
      if (ts.isVariableDeclaration(n) && n.initializer) bind(n.name, value(n.initializer, f), f);
      else if (ts.isBinaryExpression(n)) {
        const op = n.operatorToken.kind;
        const target = unwrap(n.left);
        const assigns = op === ts.SyntaxKind.EqualsToken || op === ts.SyntaxKind.QuestionQuestionEqualsToken ||
          op === ts.SyntaxKind.BarBarEqualsToken || op === ts.SyntaxKind.AmpersandAmpersandEqualsToken;
        const writes = op >= ts.SyntaxKind.FirstAssignment && op <= ts.SyntaxKind.LastAssignment;
        if (writes && ts.isIdentifier(target) && assigns) {
          const decl = resolveName(target);
          if (decl) addAll(setOf(decl), value(n.right, f));
        } else if (writes && (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)))
          store(target.expression, ts.isPropertyAccessExpression(target) ? target.name.text : nameText(target.argumentExpression),
            assigns ? value(n.right, f) : new Set(), f, n);
      } else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n) || ts.isDeleteExpression(n))) {
        const target = unwrap(ts.isDeleteExpression(n) ? n.expression : n.operand);
        if (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target))
          store(target.expression, ts.isPropertyAccessExpression(target) ? target.name.text : nameText(target.argumentExpression), new Set(), f, n);
      } else if (ts.isObjectLiteralExpression(n)) {
        const s = site(n, f, "object");
        for (const p of n.properties) {
          if (ts.isPropertyAssignment(p)) {
            addKey(s, nameText(p.name));
            addAll(contentOf(s), value(p.initializer, f));
          } else if (ts.isShorthandPropertyAssignment(p)) {
            addKey(s, nameText(p.name));
            addAll(contentOf(s), identifierValue(p.name, f));
          } else if (ts.isSpreadAssignment(p)) {
            addKey(s, null);
            addAll(contentOf(s), reads(value(p.expression, f)));
          } else if (functionLike(p)) {
            addKey(s, ts.isMethodDeclaration(p) || ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p) ? nameText(p.name) : null);
            addAll(contentOf(s), [site(p, f, "closure")]);
            const code = codeOf.get(p);
            if (code) addAll(setOf(code.receiver), [s]);
          }
        }
      } else if (ts.isArrayLiteralExpression(n)) {
        const s = site(n, f, "array");
        for (const e of n.elements) addAll(contentOf(s), ts.isSpreadElement(e) ? reads(value(e.expression, f)) : value(e, f));
      } else if (ts.isReturnStatement(n) && n.expression) {
        const c = enclosingCode(n);
        if (c) addAll(setOf(c.result), value(n.expression, f));
      } else if (ts.isArrowFunction(n) && !ts.isBlock(n.body)) {
        const c = codeOf.get(n);
        if (c) addAll(setOf(c.result), value(n.body, f));
      } else if (ts.isThrowStatement(n)) {
        const tokens = value(n.expression, f);
        addAll(thrown, tokens);
        for (const c of enclosing(componentAt(n, f))) cross(f, n, c, "out", "thrown", false, tokens, n.expression);
      } else if (ts.isCatchClause(n) && n.variableDeclaration) {
        const tokens = new Set([...thrown, ...enclosing(componentAt(n, f)).map((c) => INCOMING + c)]);
        bind(n.variableDeclaration.name, tokens, f);
        for (const c of enclosing(componentAt(n, f))) cross(f, n.variableDeclaration, c, "in", "caught", false, tokens, null);
      } else if (ts.isForOfStatement(n) && ts.isVariableDeclarationList(n.initializer))
        for (const d of n.initializer.declarations) bind(d.name, reads(value(n.expression, f)), f);
      else if (ts.isPropertyDeclaration(n) && n.initializer && n.parent && classLike(n.parent)) {
        const statics = !!n.modifiers?.some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        const ctor = codeOf.get(constructorOf(n.parent));
        const holders = statics ? new Set([site(n.parent, f, "closure")]) : ctor ? setOf(ctor.receiver) : instancesOf(n.parent);
        for (const t of sitesOf(holders)) {
          addKey(t, nameText(n.name));
          addAll(contentOf(t), value(n.initializer, f));
        }
      } else if (ts.isCallExpression(n) || ts.isNewExpression(n)) call(n, f);
      n.forEachChild(visit);
    };
    visit(f.source);
  };
  const instanceSites = new Map<Node, Set<number>>();
  const instancesOf = (c: Node): Set<number> => {
    let s = instanceSites.get(c);
    if (!s) instanceSites.set(c, s = new Set());
    return s;
  };
  const store = (receiverExpr: Node, key: string | null, tokens: Set<number>, f: File, at: Node): void => {
    const receiver = value(receiverExpr, f);
    for (const t of receiver) {
      if (t >= INCOMING) {
        const c = t - INCOMING;
        let s = incomingKeys.get(c);
        if (!s) incomingKeys.set(c, s = new Set());
        if (!s.has(key)) { s.add(key); changed = true; }
        cross(f, at, c, "out", { field: { key } }, false, tokens, at);
      } else {
        const s = sites[t];
        if (s?.kind !== "array" || key === null || !/^\d+$/.test(key)) addKey(t, s?.kind === "array" && key === null ? "[]" : key);
        addAll(contentOf(t), tokens);
      }
    }
  };
  const call = (n: Node, f: File): void => {
    if (!(ts.isCallExpression(n) || ts.isNewExpression(n))) return;
    const args = n.arguments ?? [];
    const { tokens, receiver } = calleeTokens(n.expression, f);
    let codeTargets = 0;
    for (const t of sitesOf(tokens)) {
      const s = sites[t];
      if (!s || !(functionLike(s.node) || classLike(s.node))) continue;
      codeTargets++;
      if (ts.isNewExpression(n) && classLike(s.node)) {
        const i = site(n, f, "instance");
        classOfInstance.set(i, s.node);
        addAll(setOf(n), [i]);
        for (let c: Node | undefined = s.node; c; c = baseOf(c, f)) {
          addAll(instancesOf(c), [i]);
          const ctor = codeOf.get(constructorOf(c));
          if (ctor) addAll(setOf(ctor.receiver), [i]);
          callCode(c, args, f, n, null);
        }
      } else callCode(s.node, args, f, n, receiver);
    }
    const outside = incomingOf(tokens);
    if (outside.length > 0) {
      const types = calleeParameterTypes(n.expression);
      for (const c of outside) {
        args.forEach((a, i) => cross(f, a, c, "out", { argument: { call: span(f, n), index: i } },
          readOnly(types[i], f), ts.isSpreadElement(a) ? reads(value(a.expression, f)) : value(a, f), a));
        addAll(setOf(n), [INCOMING + c]);
        cross(f, n, c, "in", { callResult: { call: span(f, n) } }, false, new Set([INCOMING + c]), null);
      }
    }
    if (codeTargets === 0 && outside.length === 0) {
      // A native: its result a site of its own, or its receiver, an argument
      // or what they hold; its receiver may hold its arguments; a closure it
      // is given may be called with any of these.
      const result = site(n, f, "native");
      const given = new Set<number>(receiver ?? []);
      for (const a of args) for (const t of ts.isSpreadElement(a) ? reads(value(a.expression, f)) : value(a, f)) given.add(t);
      const all = new Set([result, ...given, ...reads(given)]);
      for (const a of args) for (const t of sitesOf(value(a, f))) {
        const s = sites[t];
        if (s && functionLike(s.node)) {
          const code = codeOf.get(s.node);
          if (code) {
            for (const p of code.params) bindParameter(p, all, code.file);
            for (const t of setOf(code.result)) all.add(t);
          }
        }
      }
      for (const t of sitesOf(receiver ?? [])) {
        const s = sites[t];
        addAll(contentOf(t), given);
        if (s && s.kind !== "array") addKey(t, null);
      }
      addAll(setOf(n), all);
    }
  };

  // The rounds: flow, members' seeds, marks, until nothing grows.
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
  for (let round = 0; changed && round < 10000; round++) {
    changed = false;
    roundValues = new Map();
    // Members enter from outside: their parameters and receivers, crossing in.
    for (const [c, ms] of members) for (const m of ms) {
      const code = codeOf.get(m);
      if (!code) continue;
      code.params.forEach((p, i) => {
        bindParameter(p, new Set([INCOMING + c]), code.file);
        cross(code.file, p, c, "in", { parameter: { code: span(code.file, code.node), index: i } },
          readOnly(typeOfParameter(p), code.file), new Set([INCOMING + c]), null);
      });
      if (!ts.isArrowFunction(m)) addAll(setOf(code.receiver), [INCOMING + c]);
      cross(code.file, code.node, c, "out", { result: { code: span(code.file, code.node) } },
        readOnly(resultType(code.node), code.file), setOf(code.result), code.result);
    }
    // Exported bindings cross out of their module, and of the package where
    // the module is an entry module.
    for (const f of files) for (const s of f.source.statements) {
      if (!ts.isVariableStatement(s) || !exported(s)) continue;
      for (const d of s.declarationList.declarations) for (const id of boundNames(d.name)) {
        if (!ts.isIdentifier(id)) continue;
        const outs = [f.module, ...(packageIndex !== null && entryModules.includes(f.absolute) ? [packageIndex] : [])];
        for (const c of outs) cross(f, id, c, "out", { binding: { name: id.text } }, readOnly(d.type, f), setOf(id), id);
      }
    }
    for (const f of files) walk(f);
    // Marks: crossings out raise what they reach; holds by bindings and
    // storage raise what they hold.
    const reach = (tokens: Iterable<number>, c: number, m: Mark): void => {
      const work = sitesOf(tokens);
      for (let t = work.pop(); t !== undefined; t = work.pop()) {
        const s = sites[t];
        if (!s || !within(s.component, c)) continue;
        if (raise(t, c, m)) work.push(...sitesOf(contents.get(t) ?? []));
      }
    };
    for (const x of crossings.values()) if (x.direction === "out") reach(x.tokens, x.component, x.readOnly ? "exposed" : "released");
    for (const [decl, tokens] of sets) {
      if (!ts.isIdentifier(decl)) continue;
      const holder = holderOf(decl);
      const heldBy = holdsOf(decl);
      if (!holder || heldBy === null || !(ts.isSourceFile(holder) || captured.has(decl))) continue;
      for (const t of sitesOf(tokens)) {
        const s = sites[t];
        if (!s) continue;
        for (const c of enclosing(s.component)) {
          if (within(heldBy, c)) raise(t, c, "internal");
          else {
            const f = fileAt(decl);
            if (f) cross(f, decl, c, "out", { binding: { name: decl.text } }, false, new Set([t]), decl);
          }
        }
      }
    }
    for (const [t, held] of contents) {
      const s = sites[t];
      if (!s) continue;
      for (const c of enclosing(s.component)) {
        const m = markOf(t, c);
        if (m === "local") continue;
        for (const u of sitesOf(held)) {
          const v = sites[u];
          if (v && within(v.component, c)) raise(u, c, m);
        }
      }
    }
    // Escapes: a closure of a component's code reached by a crossing out of it.
    for (const [t, s] of sites.entries()) {
      if (!functionLike(s.node)) continue;
      for (const c of enclosing(s.component)) if (rank(markOf(t, c)) >= rank("exposed") && !memberOf(c).has(s.node)) {
        memberOf(c).add(s.node);
        changed = true;
      }
    }
  }
  // A record of a site exposed for a component may have every key a write of
  // that component's code adds to an incoming value.
  for (const [c, written] of incomingKeys)
    for (let t = 0; t < sites.length; t++)
      if (markOf(t, c) === "exposed") for (const k of written) addKey(t, k);

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
  const valueIndex = new Map<Node, number>();
  const values: ComponentsAst["values"] = [];
  const valueOf = (n: Node, tokens: Set<number>): number => {
    const known = valueIndex.get(n);
    if (known !== undefined) return known;
    const f = fileAt(n);
    if (!f) return -1;
    valueIndex.set(n, values.length);
    values.push({ module: f.location, pos: span(f, n), sites: sitesOf(tokens).sort((a, b) => a - b),
      incoming: incomingOf(tokens).sort((a, b) => a - b) });
    return values.length - 1;
  };
  for (const [decl, tokens] of sets) if (ts.isIdentifier(decl) && decl.parent && !ts.isImportSpecifier(decl.parent)) valueOf(decl, tokens);
  const crossingList: CrossingAst[] = [...crossings.values()].map((x) => {
    const index = x.node === null ? -1 : valueOf(x.node, x.tokens);
    return { module: x.module, at: x.at, component: x.component, direction: x.direction, position: x.position,
      readOnly: x.readOnly, value: index < 0 ? null : index };
  });
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
      work.push(...sitesOf(contents.get(t) ?? []));
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
  const codesList = codes.map((c) => ({ module: c.file.location, pos: span(c.file, c.node), component: c.component }));
  const siteList: SiteAst[] = sites.map((s, t) => ({ module: s.file.location, pos: span(s.file, s.node), kind: s.kind,
    keys: [...(keys.get(t) ?? [])].sort(), anyKey: anyKey.has(t),
    marks: enclosing(s.component).map((c) => ({ component: c, mark: markOf(t, c) })) }));
  return { components, codes: codesList, sites: siteList, values, crossings: crossingList, escapes, clients,
    guarantees: input.guarantees() };
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
