/** Family activation (HOST-FAMILIES.md, "Activation"): the active family
 * descriptions, each one's installation as Node resolves it from the
 * description's data and checked against the description's digest (C0), and
 * its guard table activated over that installation. Every family activates
 * through its description; the compiler contract additionally supplies the
 * entry points whose enum exports C1 audits. */
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import { join, relative, resolve, sep } from "node:path";
import type { FamilyDescription, GuardEntry, GuardTable } from "./host-families.mts";
import { guardClosure } from "./guard-closure.mts";
import { compilerApiFamily, hostEnumModules } from "./compiler-api.mts";
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";
import { openFrontEndCompiler, releaseCompiler } from "./compiler-channel.mts";
import { toolFailureOf } from "./thrown.mts";
import { pathToFileHref } from "./url-strings.mts";
// files.mts makes every file-system failure a tool failure.
import { findPackage, listDirectory, loadModule, manifestMember, moduleLocation, nodeResolve, orAbsent, readBytes, readText, realPath, remembered,
  runtimeConditions, type Remembered } from "./files.mts";
import type { Json } from "./calculus.mts";
export { nodeResolve, runtimeConditions } from "./files.mts";

/** The reviewed family descriptions the front end activates: each a
 * description of the trusted host contracts, contributed by the contract
 * file of its package. */
export const reviewedFamilies: readonly FamilyDescription[] = [compilerApiFamily];

/** The descriptions a test activates in place of the reviewed ones
 * (`useFamiliesForTests`); no entry point of the pipeline sets them. */
let substituted: readonly FamilyDescription[] | null = null;

/** Tests only: activate `descriptions` in place of the reviewed ones, until
 * called again with null. */
export function useFamiliesForTests(descriptions: readonly FamilyDescription[] | null): void {
  substituted = descriptions;
}

/** The active descriptions. */
export function activeFamilies(): readonly FamilyDescription[] {
  return substituted ?? reviewedFamilies;
}

/** The repository's root, against which a description's installation is
 * named. */
const repository = resolve(moduleLocation(import.meta.dirname), "..");

/** The declaration files of the package installed at `root`, the
 * installation's inventory: every `.d.ts`, `.d.mts` and `.d.cts` file under
 * the package's real directory, reached without following a symbolic link
 * and outside a nested `node_modules`, each its path from the package root.
 * A declaration of an arbitrary extension (`.d.<ext>.ts`) is refused: no
 * reading rule covers its module. */
function declarationInventory(root: string): string[] {
  const real = realPath(root);
  const files: string[] = [];
  const walk = (directory: string): void => {
    for (const entry of listDirectory(directory)) {
      const path = join(directory, entry.name);
      if (entry.isSymbolicLink()) continue;
      if (entry.isDirectory()) {
        if (entry.name !== "node_modules") walk(path);
      } else if (/\.d\.[^./]+\.ts$/.test(entry.name))
        throw Error(`the package at ${real} holds ${relative(real, path)}, a declaration of an arbitrary extension, which no reading rule covers`);
      else if (/\.d\.[mc]?ts$/.test(entry.name)) files.push(relative(real, path).split(sep).join("/"));
    }
  };
  walk(real);
  return files.sort();
}

/** The digest of the declarations of the package installed at `root` (C0):
 * the SHA-256 of the package's version, a NUL, then every file of its
 * inventory (`declarationInventory`), its path from the package root, a NUL,
 * its bytes and a NUL, in path order. */
export function declarationsDigest(root: string): string {
  const real = realPath(root);
  return digestOf(real, declarationInventory(real));
}
function digestOf(real: string, inventory: readonly string[]): string {
  const hash = createHash("sha256");
  const manifest: Json = JSON.parse(readText(join(real, "package.json")));
  const member = manifestMember(manifest, "version");
  const version = member === undefined ? "" : stringOfJson(member);
  hash.update(`${version}\0`);
  for (const file of inventory) {
    hash.update(`${file}\0`);
    hash.update(readBytes(join(real, file)));
    hash.update("\0");
  }
  return hash.digest("hex");
}
/** `String` of a JSON value, by its arms: a primitive as `String` converts
 * it; an array as `Array.prototype.toString` joins its elements with
 * commas, `null` as the empty string; an object through
 * `Object.prototype.toString`, `"[object Object]"`, unless it owns a
 * `toString`, which, as JSON data, is not callable, so that `String` finds
 * no callable conversion (its `valueOf` returns the object) and throws a
 * `TypeError`, with the message Node gives. */
function stringOfJson(value: Json): string {
  if (typeof value !== "object" || value === null) return String(value);
  if (Array.isArray(value)) return value.map((x: Json) => (x === null ? "" : stringOfJson(x))).join(",");
  if (Object.hasOwn(value, "toString")) throw new TypeError("Cannot convert object to primitive value");
  return "[object Object]";
}

/** The directory of a description's package: the package of the
 * description's name, as Node's `node_modules` lookup finds its manifest
 * from the description's directory (`installation.from`, relative to the
 * repository's root), its real path. A package not found is refused. */
const roots = new Map<string, Remembered<string>>();
export function installationRoot(description: FamilyDescription): string {
  const from = resolve(repository, description.installation.from);
  return remembered(roots, `${description.package.name}\0${from}`, () => {
    const root = findPackage(description.package.name, from);
    if (root === null)
      throw Error(`the family ${description.marker}'s package ${description.package.name} does not resolve from ${description.installation.from}`);
    return root;
  });
}

/** The installations checked, by root and the digest checked against: the
 * real paths of the inventory hashed. */
const checkedInstallations = new Map<string, Remembered<ReadonlySet<string>>>();

/** A description's installation, checked once per process: its manifest
 * names the description's package and version, and its declarations have the
 * description's digest. A mismatch refuses every use of the family, as a
 * package other than the one reviewed. */
export function checkedInstallation(description: FamilyDescription): string {
  checkedInventory(description);
  return installationRoot(description);
}

/** The real paths of a checked installation's inventory, the declarations
 * its digest covers. */
function checkedInventory(description: FamilyDescription): ReadonlySet<string> {
  const root = installationRoot(description);
  const key = `${root}\0${description.package.name}\0${description.package.version}\0${description.installation.digest}`;
  return remembered(checkedInstallations, key, () => checkInventory(description, root));
}
function checkInventory(description: FamilyDescription, root: string): ReadonlySet<string> {
  const manifest: Json = JSON.parse(readText(join(root, "package.json")));
  const name = manifestMember(manifest, "name") ?? null;
  const version = manifestMember(manifest, "version") ?? null;
  if (name !== description.package.name || version !== description.package.version)
    throw Error(`the package at ${root} is not the family ${description.marker}'s ${description.package.name} ` +
      `${description.package.version}: its manifest names ${stringOfJson(name)} ${stringOfJson(version)}`);
  const inventory = declarationInventory(root);
  const digest = digestOf(root, inventory);
  if (digest !== description.installation.digest)
    throw Error(`the package at ${root} is not the one the family ${description.marker} was reviewed against: ` +
      `its declarations' digest is ${digest}, the description's ${description.installation.digest}`);
  return new Set(inventory.map(file => join(root, ...file.split("/"))));
}

/** The active descriptions with their installations' roots, each marker and
 * each root owned by one description. */
function installations(): readonly { description: FamilyDescription; root: string }[] {
  const active = activeFamilies();
  const found = active.flatMap(description => [{ description, root: installationRoot(description) }]);
  for (const [i, a] of found.entries())
    for (const b of found.slice(i + 1)) {
      if (a.description.marker === b.description.marker)
        throw Error(`two active family descriptions own the marker ${a.description.marker}`);
      if (a.root === b.root || a.root.startsWith(b.root + sep) || b.root.startsWith(a.root + sep))
        throw Error(`the families ${a.description.marker} and ${b.description.marker} share the installation ${a.root}`);
      // Each guard entry is one description's, so a guard's family is its
      // entry's (`familyOfGuard`).
      if (a.description.guards.guards.some(g => b.description.guards.guards.includes(g)))
        throw Error(`the families ${a.description.marker} and ${b.description.marker} share a guard entry`);
    }
  return found;
}

/** The active description whose installation's inventory holds `file`, by
 * its real path, the installation checked; null for any other file, a
 * dependency in a nested `node_modules` or a file reached only through a
 * symbolic link inside the package among them. */
export function familyOfFile(file: string): FamilyDescription | null {
  // A path that names nothing is in no installation; any other failure
  // resolving it is the tool's.
  const real = orAbsent(realPath, file);
  if (real === null) return null;
  const found = installations().find(i => real.startsWith(i.root + sep));
  if (!found) return null;
  return checkedInventory(found.description).has(real) ? found.description : null;
}

/** `file`'s path inside the installation of the active description holding
 * it, by its real path, `/`-separated; null for a file of no installation. */
export function installationPath(file: string): string | null {
  const real = orAbsent(realPath, file);
  if (real === null) return null;
  const found = installations().find(i => real.startsWith(i.root + sep));
  if (!found || !checkedInventory(found.description).has(real)) return null;
  return relative(found.root, real).split(sep).join("/");
}

/** Whether `file` is a declaration of a host package: a file of an active
 * description's installation, whose declarations have the description's
 * digest. A package elsewhere, whatever its manifest names, is no host. */
export function isHostFile(file: string): boolean {
  return familyOfFile(file) !== null;
}

/** The active description whose guard table lists `entry`. */
export function familyOfGuard(entry: GuardEntry): FamilyDescription {
  const found = activeFamilies().find(d => d.guards.guards.includes(entry));
  if (!found) throw Error(`the guard ${entry.name} is of no active family`);
  return found;
}

/** A guard table checked against the package at `root`, once per table and
 * root (HOST-FAMILIES.md, "The guard
 * table"). Its conditions are the ones Node enables in this process, and no
 * flag preserves symlinks; its entry point, through the package's name,
 * resolves as Node's own resolver resolves it (`nodeResolve`) to the module
 * the table records. Node loads that module: each entry's export is a
 * function of the entry's text, the one the module the entry records
 * exports, which declares it with that text, never assigned. Each free name
 * of that function, and of each helper it reaches, is a function of its
 * module or a named import, without attributes, that Node resolves from the
 * importing module to a module of the package and that the loaded module
 * exports: the helpers and the binding edges (importing module, local name,
 * target module, exported name) this closure reaches are exactly the
 * entry's, each helper of exactly its recorded text, also as loaded where
 * exported. `parse` gives a module's tree. A mismatch, or a load Node
 * refuses, is no table: every guard of the family is then read without
 * predicate. */
type Loaded = { entries: ReadonlyMap<string, GuardEntry>; functions: ReadonlyMap<unknown, GuardEntry>;
  modules: Map<string, ReadonlyMap<string, unknown>> };
/** The guard tables activated, by root and table, each with the
 * observations it was computed from (`remembered`). */
const activeTables = new Map<string, Map<GuardTable, Remembered<Loaded | null>>>();
export function activeGuards(table: GuardTable, root: string): ReadonlyMap<string, GuardEntry> | null {
  return loadedGuards(table, root)?.entries ?? null;
}
function loadedGuards(table: GuardTable, root: string): Loaded | null {
  const tables = activeTables.get(root) ?? new Map<GuardTable, Remembered<Loaded | null>>();
  activeTables.set(root, tables);
  return remembered(tables, table, () => activateGuards(table, root));
}
function activateGuards(table: GuardTable, root: string): Loaded | null {
  // The package's modules, read by a compiler of the check's own.
  const contents = new Map<string, string>();
  const api = openFrontEndCompiler(root, contents);
  const parse = (path: string, text: string): ts.SourceFile => {
    contents.set(path, text);
    const program = api.updateSnapshot({ openFiles: [path] }).getDefaultProjectForFile(path)?.program;
    if (program?.getSyntacticDiagnostics(path).length) throw Error(`invalid module syntax in ${path}`);
    const file = program?.getSourceFile(path);
    if (!file) throw Error(`the compiler produced no tree for ${path}`);
    return file;
  };
  let result: Loaded | null = null;
  let thrown: { error: unknown } | null = null;
  try {
    result = checkedGuards(table, root, parse);
  } catch (error) {
    // A tool failure is no mismatch: it is reported, not read as no table.
    if (toolFailureOf(error)) { thrown = { error }; throw error; }
    result = null;
  } finally {
    releaseCompiler(api, thrown);
  }
  return result;
}

function checkedGuards(table: GuardTable, root: string, parse: (path: string, text: string) => ts.SourceFile):
    Loaded | null {
  // Every specifier is resolved by Node's own resolver, from the module that
  // contains it: the entry point through the package's name, from its
  // manifest; each import from its module. A module is its path in the
  // package; a file outside it, or any error, is no table.
  const manifest: Json = JSON.parse(readText(join(root, "package.json")));
  const name = manifestMember(manifest, "name");
  if (typeof name !== "string") return null;
  // The table's conditions are the ones Node enables in this process.
  const runtime = runtimeConditions();
  if (table.conditions.length !== runtime.length || !runtime.every(c => table.conditions.includes(c))) return null;
  // Resolution that keeps symlinked paths gives modules other parents than
  // the real paths this check reads: no table.
  const flags = [...process.execArgv, ...(process.env["NODE_OPTIONS"] ?? "").split(/\s+/)];
  if (flags.some(f => f.startsWith("--preserve-symlinks"))) return null;
  const realRoot = realPath(root);
  // A module of the package as Node loads it, the instance a program
  // importing it shares; null where the load throws.
  // Each module loaded, by its URL; recognition reads these alone. A
  // module's exports are a Map by name, which holds no inherited member.
  const urlOf = (module: string): string => pathToFileHref(join(realRoot, module));
  const modules = new Map<string, ReadonlyMap<string, unknown>>();
  const load = (module: string): ReadonlyMap<string, unknown> | null => {
    if (!Object.hasOwn(table.closure.files, module)) return null;
    const known = modules.get(urlOf(module));
    if (known) return known;
    try {
      const namespace = loadModule(realRoot, join(realRoot, module));
      if (namespace === null) return null;
      modules.set(urlOf(module), namespace);
      return namespace;
    } catch {
      return null;
    }
  };
  const resolveSpecifier = (from: string, specifier: string): string | null => {
    const resolved = nodeResolve(specifier, join(root, from));
    if (resolved === null) return null;
    const module = relative(realRoot, fileURLToPath(resolved)).split(sep).join("/");
    return module.startsWith("../") || urlOf(module) !== resolved ? null : module;
  };
  const entryPoint = table.entryPoint === "." ? name : `${name}${table.entryPoint.slice(1)}`;
  if (resolveSpecifier("package.json", entryPoint) !== table.entryModule) return null;
  const trees = new Map<string, ts.SourceFile>();
  const tree = (module: string): ts.SourceFile => {
    const known = trees.get(module);
    if (known) return known;
    const parsed = parse(join(root, module), readText(join(root, module)));
    trees.set(module, parsed);
    return parsed;
  };
  // Complete executable closure, checked before Node evaluates any module.
  // The installation stays unchanged between this check and loading (T2).
  try {
    const closure = guardClosure(table.entryModule, module => readBytes(join(realRoot, module)),
      (module, text) => {
        const parsed = parse(join(realRoot, module), text);
        trees.set(module, parsed);
        return parsed;
      }, resolveSpecifier);
    if (!closure || JSON.stringify(closure) !== JSON.stringify(table.closure)) return null;
  } catch { return null; }
  // Post-load checks may only load modules in the checked closure, including
  // when a malformed table names a different declaring module or helper.
  const entryLoaded = load(table.entryModule);
  if (!entryLoaded) return null;
  // Each helper's text, by its key, which a table states once.
  const helperTexts = new Map(table.helpers);
  if (helperTexts.size !== table.helpers.length) return null;
  // The names a module assigns anywhere: an assignment, compound or not, or
  // an update of a plain name.
  const assignedIn = new Map<string, Set<string>>();
  const assigned = (module: string): Set<string> => {
    const known = assignedIn.get(module);
    if (known) return known;
    const names = new Set<string>();
    const visit = (n: Node): void => {
      if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
          n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && ts.isIdentifier(n.left)) names.add(n.left.text);
      if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && ts.isIdentifier(n.operand) &&
          (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
        names.add(n.operand.text);
      n.forEachChild(visit);
    };
    visit(tree(module));
    assignedIn.set(module, names);
    return names;
  };
  // A module's function declaration named `name`, the one statement
  // declaring it there and never assigned.
  const functionOf = (module: string, name: string): ts.FunctionDeclaration | null => {
    const found = tree(module).statements.filter((s): s is ts.FunctionDeclaration =>
      ts.isFunctionDeclaration(s) && s.name?.text === name);
    const [only] = found;
    return only && found.length === 1 && only.body && !assigned(module).has(name) ? only : null;
  };
  // A module's named imports: each local name, the module it resolves to
  // and the name it imports.
  // An import with attributes is refused: no import of the closure has one.
  const importsOf = (module: string): Map<string, { module: string; name: string }> | null => {
    const out = new Map<string, { module: string; name: string }>();
    for (const s of tree(module).statements) {
      if (!ts.isImportDeclaration(s) || !ts.isStringLiteral(s.moduleSpecifier)) continue;
      if (s.attributes) return null;
      const bindings = s.importClause?.namedBindings;
      if (s.importClause?.name || !bindings || !ts.isNamedImports(bindings)) continue;
      const from = resolveSpecifier(module, s.moduleSpecifier.text);
      if (!from) continue;
      for (const e of bindings.elements)
        out.set(e.name.text, { module: from, name: e.propertyName ? e.propertyName.getText(tree(module)) : e.name.text });
    }
    return out;
  };
  // The free names of a function's body: every name read but a property's
  // and those the function declares.
  const freeNames = (f: ts.FunctionDeclaration): Set<string> => {
    const declared = new Set(f.parameters.flatMap(p => ts.isIdentifier(p.name) ? [p.name.text] : []));
    const names = new Set<string>();
    const visit = (n: Node): void => {
      if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name)) declared.add(n.name.text);
      if (ts.isPropertyAccessExpression(n)) { visit(n.expression); return; }
      if (ts.isIdentifier(n)) names.add(n.text);
      n.forEachChild(visit);
    };
    if (f.body) visit(f.body);
    return new Set([...names].filter(n => !declared.has(n)));
  };
  const textOf = (module: string, f: ts.FunctionDeclaration): string => f.getText(tree(module)).trim();
  // A loaded function of the text a module declares it with.
  const runs = (value: unknown, text: string): boolean =>
    typeof value === "function" && value.toString() === text.replace(/^export /, "");
  const entries = new Map<string, GuardEntry>();
  const functions = new Map<unknown, GuardEntry>();
  for (const entry of table.guards) {
    // The function the entry point exports, as Node loads it, is the one
    // the declaring module exports, of the entry's text.
    const f = functionOf(entry.module, entry.name);
    const declaring = load(entry.module);
    const loaded = entryLoaded.get(entry.name);
    if (!f || textOf(entry.module, f) !== entry.text || !runs(loaded, entry.text) || !declaring ||
        declaring.get(entry.name) !== loaded) return null;
    // The dependency closure: helpers and binding edges reached.
    const helpers = new Set<string>();
    const edges = new Set<string>();
    const recordedEdges = new Set(entry.edges.map(e => JSON.stringify(e)));
    const pending: { module: string; f: ts.FunctionDeclaration }[] = [{ module: entry.module, f }];
    for (let next = pending.pop(); next; next = pending.pop()) {
      const { module } = next;
      const imports = importsOf(module);
      if (!imports) return null;
      for (const name of freeNames(next.f)) {
        const local = functionOf(module, name);
        const imported: { module: string; name: string } | undefined = imports.get(name);
        if (local) {
          const key = `${module}#${name}`;
          if (helperTexts.get(key) !== textOf(module, local)) return null;
          if (!helpers.has(key)) { helpers.add(key); pending.push({ module, f: local }); }
        } else if (imported) {
          const edge = JSON.stringify([module, name, imported.module, imported.name]);
          // A module outside the recorded closure is never loaded.
          if (!recordedEdges.has(edge)) return null;
          edges.add(edge);
          // The binding the target module exports, as Node loads it.
          const target = load(imported.module);
          const value = target?.get(imported.name);
          if (value === undefined) return null;
          const helper = functionOf(imported.module, imported.name);
          if (helper) {
            const key = `${imported.module}#${imported.name}`;
            if (helperTexts.get(key) !== textOf(imported.module, helper) || !runs(value, textOf(imported.module, helper)))
              return null;
            if (!helpers.has(key)) { helpers.add(key); pending.push({ module: imported.module, f: helper }); }
          }
        } else return null;
      }
    }
    if (helpers.size !== entry.helpers.length || !entry.helpers.every(h => helpers.has(h)) ||
        edges.size !== recordedEdges.size || ![...edges].every(e => recordedEdges.has(e))) return null;
    entries.set(entry.name, entry);
    functions.set(loaded, entry);
  }
  return { entries, functions, modules };
}

/** What Node binds when the module at `from` imports `imported` from
 * `specifier`, read without loading anything: Node's own resolver resolves
 * the specifier from that module to a URL, with no query or fragment. Where
 * that URL is one of the modules an active family's contract checks, the
 * binding is a listed guard where its export there is the very
 * function activation checked (`entry`, else `null`); any other file of an
 * active installation binds nothing (`null`), unloaded; a module outside
 * every installation is named by its real path (`program`), which may
 * re-export one. */
export function importedGuard(from: string, specifier: string, imported: string):
    { entry: GuardEntry | null } | { program: string } | null {
  const bound = importedExport(from, specifier, imported);
  return bound && bound.description !== undefined ? { entry: guardOfExport(bound.description, bound.value) } : bound;
}

/** What Node binds for an import, read as `importedGuard` reads it: where
 * Node resolves the specifier to a module in the family's checked inventory,
 * the value that module exports under `imported`, with the family;
 * a module outside every installation by its real path (`program`); any
 * other binding none. */
export function importedExport(from: string, specifier: string, imported: string):
    { description: FamilyDescription; value: unknown } | { program: string; description?: never } | null {
  const resolved = nodeResolve(specifier, from);
  if (resolved === null) return null;
  const path = orAbsent(realPath, fileURLToPath(resolved));
  if (path === null) return null;
  for (const description of activeFamilies()) {
    const root = installationRoot(description);
    if (relative(root, path).split(sep)[0] === "..") continue;
    checkedInstallation(description);
    const namespace = activatedModules(description).get(resolved);
    return namespace?.has(imported) ? { description, value: namespace.get(imported) } : null;
  }
  return { program: path };
}

/** Activated family modules, including the compiler entry points whose enum
 * exports C1 audits. All binding recognition uses this one module inventory. */
function activatedModules(description: FamilyDescription): ReadonlyMap<string, ReadonlyMap<string, unknown>> {
  const root = checkedInstallation(description);
  const modules = new Map<string, ReadonlyMap<string, unknown>>(loadedGuards(description.guards, root)?.modules);
  if (description === compilerApiFamily) {
    for (const { specifier, namespace } of hostEnumModules) {
      const url = nodeResolve(specifier, moduleLocation(import.meta.filename));
      if (url !== null) modules.set(url, namespace);
    }
  }
  return modules;
}

/** The audited enum object exported by an activated module. Compiler enums
 * are compared with their declarations by C1; family tags by tagEnumMatches. */
export function hostEnumObject(description: FamilyDescription, name: string): unknown {
  checkedInstallation(description);
  if (description === compilerApiFamily) {
    for (const { namespace } of hostEnumModules)
      if (namespace.has(name)) return namespace.get(name);
  }
  if (name !== description.tag.constants.enum) return undefined;
  return tagEnumObject(description);
}

/** The listed guard of a family whose function activation checked is
 * `value`, or null. */
export function guardOfExport(description: FamilyDescription, value: unknown): GuardEntry | null {
  return loadedGuards(description.guards, installationRoot(description))?.functions.get(value) ?? null;
}

/** A family's tag enum object: the export of its name from the family's
 * activated entry point, as Node loaded it; undefined where the guard table
 * is not active. */
export function tagEnumObject(description: FamilyDescription): unknown {
  const root = checkedInstallation(description);
  const table = description.guards;
  const entry = loadedGuards(table, root)?.modules.get(pathToFileHref(join(realPath(root), table.entryModule)));
  return entry?.get(description.tag.constants.enum);
}

/** Whether a family's tag enum, declared with the members `declared` (each
 * its name and the value TypeScript computes), is the runtime object the
 * family's activated entry point exports under the enum's name, as Node
 * loaded it (HOST-FAMILIES.md, "Activation"; C1 of the compiler API, for
 * every family, `enumObjectMatches`). False where the family's guard table
 * is not active, or the entry point exports no such object. */
export function tagEnumMatches(description: FamilyDescription, declared: readonly { name: string; value: string | number | undefined }[]): boolean {
  return enumObjectMatches(tagEnumObject(description), declared);
}

/** Whether `object` is the object of an enum declared with the members
 * `declared`, each its name and the value TypeScript computes, as
 * TypeScript's emit builds it (SOURCE-CONTRACTS.md, "Enums",
 * `emitted-enum`): each member an own data property holding its value; for
 * each numeric value, the own data property its `ToString` names holding the
 * name of a member with that value, the reverse mapping; and no other own
 * key. */
export function enumObjectMatches(object: unknown, declared: readonly { name: string; value: string | number | undefined }[]): boolean {
  if (typeof object !== "object" || object === null || !declared.length) return false;
  const members = new Map<string, string | number>();
  for (const { name, value } of declared) {
    if (value === undefined) return false;
    const property = Object.getOwnPropertyDescriptor(object, name);
    if (!property || !("value" in property) || property.value !== value) return false;
    members.set(name, value);
  }
  // A reverse key's own data property, holding the name of a member with
  // the value its key names.
  const reverse = (key: string): boolean => {
    const property = Object.getOwnPropertyDescriptor(object, key);
    return !!property && "value" in property && typeof property.value === "string" &&
      String(members.get(property.value)) === key && typeof members.get(property.value) === "number";
  };
  return [...members.values()].every(value => typeof value !== "number" || reverse(String(value))) &&
    Reflect.ownKeys(object).every(key => typeof key === "string" && (members.has(key) || reverse(key)));
}

/** The entry of the listed guard of a declaration's name, for the run's tag
 * selection alone, which a further tag only widens: the function `name` of
 * the declaration file `file`, which the entry's module declares, in the
 * guard table of the family whose installation holds `file`. */
export function selectionGuard(file: string, name: string): GuardEntry | null {
  const description = familyOfFile(file);
  if (!description) return null;
  const root = installationRoot(description);
  const entry = activeGuards(description.guards, root)?.get(name);
  if (!entry) return null;
  const declared = relative(root, realPath(file)).split(sep).join("/");
  return declared === entry.module.replace(/\.js$/, ".d.ts") ? entry : null;
}

