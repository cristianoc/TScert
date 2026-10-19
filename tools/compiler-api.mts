/** The compiler API as a host library (COMPILER-API.md): the reviewed
 * contract under which code reading TypeScript's trees and checker through
 * the package `typescript` is verified.
 *
 * The package's declarations are read on use, by the declaration reader's
 * rules for host declarations; this file states what a declaration cannot:
 * which package is the host, and which of its enums the contract reads as
 * values. Each entry is checked against the installed package by
 * `tests/compiler-api.mts`. */
import { createHash } from "node:crypto";
import { dirname, join, relative, sep } from "node:path";
import type { DeclarationIdentity, TypeTerm } from "./declaration-types.mts";
import type { FamilyDescription, GuardEntry, GuardTable } from "./host-families.mts";
import { compilerApiGuards } from "./compiler-api-guards.mts";
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";
import { nameOf } from "./syntax.mts";
import { openCompiler, releaseCompiler } from "./compiler-channel.mts";
import { toolFailureOf } from "./thrown.mts";
// files.mts makes every file-system failure a tool failure.
import { listDirectory, orAbsent, readBytes, readText, realPath, resolveModule } from "./files.mts";

/** Reading rule 2: a property of a host declaration declared `any` states
 * nothing, and is read as an optional member of type `unknown`, as the
 * syntax tree's brands (`_expressionBrand: any`), which no runtime node
 * owns, are. Whether `member` is such a property. */
export function readsAsOptionalUnknown(member: Node): boolean {
  const name = nameOf(member);
  const type = ts.isPropertySignatureDeclaration(member) || ts.isPropertyDeclaration(member) ? member.type : undefined;
  return !!name && ts.isIdentifier(name) && type?.kind === ts.SyntaxKind.AnyKeyword;
}

/** The host package: its name and the version the contract was reviewed
 * against (`tools/package-lock.json`). */
export const hostPackage = { name: "typescript", version: "7.0.2" } as const;

/** The host enums the contract reads as values: each a `declare enum` the
 * package exports through its `#enums/*` imports, its declaration file
 * `dist/enums/<file>.enum.d.ts` and its runtime object, which Node loads
 * under the `default` condition, `dist/enums/<file>.js`. C1 checks that the
 * runtime object holds exactly the members and values the declaration
 * states (T5). An enum of the package outside this list is refused where
 * it is read as a value: `CharacterCodes.ogham` is 5760 in its declaration
 * and 5765 at run time. */
export const hostEnums: readonly { name: string; file: string }[] = [
  { name: "SyntaxKind", file: "syntaxKind" },
  { name: "NodeFlags", file: "nodeFlags" },
  { name: "TypeFlags", file: "typeFlags" },
  { name: "SymbolFlags", file: "symbolFlags" },
  { name: "SignatureKind", file: "signatureKind" },
  { name: "ElementFlags", file: "elementFlags" },
  { name: "DiagnosticCategory", file: "diagnosticCategory" },
];

/** The members of host types whose read allocates (reading rule 1), each
 * with the interface declaring it and the declaration text it was reviewed
 * against: `jsDoc` builds a fresh array on each read
 * (`node.generated.js:221`). The declaration reader omits each from its host
 * type's shape, so every read of it is a read of a member the type does not
 * state. */
export const allocatingMembers: readonly { owner: string; name: string; text: string }[] = [
  { owner: "Node", name: "jsDoc", text: "readonly jsDoc?: readonly Node[] | undefined;" },
];

/** The compiler API's family description (HOST-FAMILIES.md, "The compiler
 * API"): the syntax tree's nodes, tagged by `kind`. The generic rule names
 * every generic node declaration; `KeywordExpression` gives the shapes of
 * `null`, `true`, `false`, `this`, `super` and `import`, which the
 * declarations make expressions. Each correction is a field the
 * declarations state required and the runtime leaves absent (COMPILER-API.md,
 * "Corrections"). */
export const compilerApiFamily: FamilyDescription = {
  package: hostPackage.name,
  marker: "RemoteNode",
  root: { name: "Node", form: "inheritance", text: "export interface Node extends ReadonlyTextRange {" },
  tag: { field: "kind", primitive: "number", constants: { enum: "SyntaxKind" } },
  table: [
    { rule: "literal" },
    { rule: "generic", declarations: ["Token", "KeywordTypeNode", "KeywordExpression"] },
    { rule: "base", declaration: "NodeBase" },
  ],
  corrections: [
    { kind: "PropertySignature", owner: "PropertySignatureDeclaration", member: "initializer", text: "readonly initializer: Expression;" },
    { kind: "PropertyAssignment", owner: "PropertyAssignment", member: "type", text: "readonly type: TypeNode;" },
    { kind: "ShorthandPropertyAssignment", owner: "ShorthandPropertyAssignment", member: "type", text: "readonly type: TypeNode;" },
    { kind: "ExportAssignment", owner: "ExportAssignment", member: "type", text: "readonly type: TypeNode;" },
    { kind: "DefaultClause", owner: "DefaultClause", member: "expression", text: "readonly expression: Expression;" },
    { kind: "NoSubstitutionTemplateLiteral", owner: "TemplateLiteralLikeNodeBase", member: "rawText", text: "readonly rawText: string;" },
    { kind: "NoSubstitutionTemplateLiteral", owner: "TemplateLiteralLikeNodeBase", member: "templateFlags", text: "readonly templateFlags: TokenFlags;" },
    { kind: "SourceFile", owner: "Node", member: "parent", text: "readonly parent: Node;" },
    { kind: "TaggedTemplateExpression", owner: "TaggedTemplateExpression", member: "questionDotToken", text: "readonly questionDotToken: QuestionDotToken;" },
    { kind: "JSDocTemplateTag", owner: "JSDocTemplateTag", member: "constraint", text: "readonly constraint: Node;" },
  ],
  guards: compilerApiGuards,
};

let familyStandIn: FamilyDescription | null = null;
/** Tests only: read the compiler API's family through `description` until
 * called again with null. */
export function useFamilyDescriptionForTests(description: FamilyDescription | null): void {
  familyStandIn = description;
}
/** The description the declaration reader reads the compiler API's family
 * through: `compilerApiFamily`, or a test's stand-in. */
export function hostFamily(): FamilyDescription {
  return familyStandIn ?? compilerApiFamily;
}

/** The interfaces of the host package that are host types by themselves
 * (reading rule 1): `Node`, every node shape reaching it through `extends`,
 * `NodeArray`, and the sync API's `Type`, its sub-interfaces reaching it.
 * Every class the package declares is a host type too. */
export const hostTypeRoots: readonly string[] = ["Node", "NodeArray", "Type"];

/** The branded strings (COMPILER-API.md, reading rule 5): host-introduced
 * types whose values are strings the package produces. Read as `string` where
 * the client receives one; a host signature's parameter mentioning one is
 * refused (L5), since the calculus has no opaque primitive type to admit only
 * the package's own values. Each entry is its declaration as reviewed. */
export const brandedTypes: readonly { name: string; text: string }[] = [
  { name: "Path", text: "export type Path = string & {\n    __pathBrand: any;\n};" },
  { name: "__String", text: "export type __String = (string & {\n    __escapedIdentifier: void;\n}) | InternalSymbolName;" },
];

/** A host-produced type with each branded string where the host produces it
 * (`out`) read as `string` (reading rule 5): a primitive result, a readonly
 * member, a callback's parameter. Where the client produces one (`out`
 * false: a parameter of a host function, a callback's result) or both
 * (`null`: a writable member, a type argument, a binder's bound), the brand
 * is an introduction obligation only a value the package produced meets,
 * which the calculus cannot state: refused (L5). A brand left unread here, as
 * a client annotation naming it or an alias of it, keeps its declared
 * definition, `string & { … }`, which no value meets and which is refused
 * where it is used. */
export function hostBrands(t: TypeTerm, out: boolean | null, brand: (id: DeclarationIdentity) => boolean,
    fail: (message: string) => never): TypeTerm {
  const go = (u: TypeTerm, o: boolean | null): TypeTerm => hostBrands(u, o, brand, fail);
  switch (t.k) {
    case "reference":
      if (brand(t.reference.target)) {
        if (out === true) return { k: "atom", name: "string", span: t.span };
        return fail(`the host's branded string ${t.reference.name} where the client would produce one: only the package produces its values (COMPILER-API.md, L5)`);
      }
      return { ...t, args: t.args.map(a => go(a, null)) };
    case "union": case "intersection": return { ...t, parts: t.parts.map(p => go(p, out)) };
    case "array": return { ...t, element: go(t.element, t.readonly ? out : null) };
    case "tuple": {
      const o = t.readonly ? out : null;
      return { ...t, required: t.required.map(e => go(e, o)), optional: t.optional.map(e => go(e, o)),
        rest: t.rest && go(t.rest, o) };
    }
    case "object":
      return { ...t, fields: t.fields.map(f => ({ ...f, type: go(f.type, f.readonly ? out : null) })),
        stringIndex: t.stringIndex && { ...t.stringIndex, value: go(t.stringIndex.value, t.stringIndex.readonly ? out : null) },
        ...(t.numberIndex ? { numberIndex: { ...t.numberIndex, value: go(t.numberIndex.value, t.numberIndex.readonly ? out : null) } } : {}),
        ...(t.symbolIndex ? { symbolIndex: { ...t.symbolIndex, value: go(t.symbolIndex.value, t.symbolIndex.readonly ? out : null) } } : {}),
        calls: t.calls.map(c => hostBrandsFunction(c, out, brand, fail)),
        ...(t.prototype ? { prototype: go(t.prototype, out) } : {}) };
    case "function": return hostBrandsFunction(t, out, brand, fail);
    case "constructor": return hostBrandsConstructor(t, out, brand, fail);
    case "pack": return { ...t, of: go(t.of, out) };
    case "scheme":
      return { ...t, binders: t.binders.map(b => ({ ...b, bound: b.bound && go(b.bound, null), default: b.default && go(b.default, null) })),
        signatures: t.signatures.map(s => s.k === "function" ? hostBrandsFunction(s, out, brand, fail)
          : hostBrandsConstructor(s, out, brand, fail)) };
    default: return t;
  }
}
function hostBrandsConstructor(t: Extract<TypeTerm, { k: "constructor" }>, out: boolean | null,
    brand: (id: DeclarationIdentity) => boolean, fail: (message: string) => never): Extract<TypeTerm, { k: "constructor" }> {
  const flip = out === null ? null : !out;
  const go = (u: TypeTerm, o: boolean | null): TypeTerm => hostBrands(u, o, brand, fail);
  return { ...t, params: t.params.map(p => go(p, flip)), rest: t.rest && go(t.rest, flip), result: go(t.result, out),
    ...(t.statics ? { statics: t.statics.map(s => ({ ...s, type: go(s.type, s.readonly ? out : null) })) } : {}) };
}
function hostBrandsFunction(t: Extract<TypeTerm, { k: "function" }>, out: boolean | null,
    brand: (id: DeclarationIdentity) => boolean, fail: (message: string) => never): Extract<TypeTerm, { k: "function" }> {
  const flip = out === null ? null : !out;
  const go = (u: TypeTerm, o: boolean | null): TypeTerm => hostBrands(u, o, brand, fail);
  return { ...t, receiver: t.receiver && go(t.receiver, flip), params: t.params.map(p => go(p, flip)),
    rest: t.rest && go(t.rest, flip), result: go(t.result, out) };
}

/** The named views of the host classes (reading rule 4): each class is read
 * through the members its view lists, each read exactly as its reviewed
 * declaration text states it; an overloaded member is the overloads listed.
 * A class the contract lists no view for has none: no member. The members
 * are the ones the front end reads (2026-10-18), but `Symbol.getExports` and
 * `getMembers`, whose `ReadonlyMap<__String, Symbol>` takes the branded key
 * from the client at `get` (reading rule 5), and `Type`'s `this is X`
 * methods, which wait for stated type guards. `Type`, an interface, has a
 * view of its own as a class does. */
export const hostViews: readonly { owner: string; members: readonly { name: string; text: string }[] }[] = [
  { owner: "API", members: [
    { name: "close", text: "close(): void;" },
    { name: "updateSnapshot", text: "updateSnapshot(params?: FromLSP extends true ? LSPUpdateSnapshotParams : UpdateSnapshotParams): Snapshot;" },
  ] },
  { owner: "Snapshot", members: [
    { name: "getDefaultProjectForFile", text: "getDefaultProjectForFile(file: DocumentIdentifier): Project | undefined;" },
    { name: "getProject", text: "getProject(configFileName: string): Project | undefined;" },
  ] },
  { owner: "Project", members: [
    { name: "checker", text: "readonly checker: Checker;" },
    { name: "compilerOptions", text: "readonly compilerOptions: CompilerOptions;" },
    { name: "configFileName", text: "readonly configFileName: string;" },
    { name: "program", text: "readonly program: Program;" },
  ] },
  { owner: "Program", members: [
    { name: "getProgramDiagnostics", text: "getProgramDiagnostics(): readonly Diagnostic[];" },
    { name: "getSemanticDiagnostics", text: "getSemanticDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];" },
    { name: "getSourceFile", text: "getSourceFile(file: DocumentIdentifier): SourceFile | undefined;" },
    { name: "getSourceFileNames", text: "getSourceFileNames(): readonly string[];" },
    { name: "getSyntacticDiagnostics", text: "getSyntacticDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];" },
    { name: "isSourceFileDefaultLibrary", text: "isSourceFileDefaultLibrary(file: SourceFile): boolean;" },
  ] },
  { owner: "Checker", members: [
    { name: "getAliasedSymbol", text: "getAliasedSymbol(symbol: Symbol): Symbol;" },
    { name: "getConstantValue", text: "getConstantValue(node: Node): string | number | undefined;" },
    { name: "getExportsOfModule", text: "getExportsOfModule(symbol: Symbol): readonly Symbol[];" },
    { name: "getImmediateAliasedSymbol", text: "getImmediateAliasedSymbol(symbol: Symbol): Symbol | undefined;" },
    { name: "getIndexInfosOfType", text: "getIndexInfosOfType(type: Type): readonly IndexInfo[];" },
    { name: "getNonNullableType", text: "getNonNullableType(type: Type): Type | undefined;" },
    { name: "getParameterType", text: "getParameterType(signature: Signature, index: number): Type | undefined;" },
    { name: "getPropertiesOfType", text: "getPropertiesOfType(type: Type): readonly Symbol[];" },
    { name: "getPropertyOfType", text: "getPropertyOfType(type: Type, name: string): Symbol | undefined;" },
    { name: "getResolvedSignature", text: "getResolvedSignature(node: Node): Signature | undefined;" },
    { name: "getReturnTypeOfSignature", text: "getReturnTypeOfSignature(signature: Signature): Type | undefined;" },
    { name: "getShorthandAssignmentValueSymbol", text: "getShorthandAssignmentValueSymbol(node: Node): Symbol | undefined;" },
    { name: "getSignaturesOfType", text: "getSignaturesOfType(type: Type, kind: SignatureKind): readonly Signature[];" },
    { name: "getSymbolAtLocation", text: "getSymbolAtLocation(node: Node): Symbol | undefined;" },
    { name: "getTypeArguments", text: "getTypeArguments(type: TypeReference): readonly Type[];" },
    { name: "getTypeAtLocation", text: "getTypeAtLocation(node: Node): Type | undefined;" },
    { name: "getTypeFromTypeNode", text: "getTypeFromTypeNode(node: TypeNode): Type | undefined;" },
    { name: "getTypeOfSymbol", text: "getTypeOfSymbol(symbol: Symbol): Type | undefined;" },
    { name: "isArrayType", text: "isArrayType(type: Type): boolean;" },
    { name: "isTupleType", text: "isTupleType(type: Type): boolean;" },
    { name: "isUndefinedSymbol", text: "isUndefinedSymbol(symbol: Symbol): boolean;" },
    { name: "isUnknownSymbol", text: "isUnknownSymbol(symbol: Symbol): boolean;" },
    { name: "resolveName", text: "resolveName(name: string, meaning: SymbolFlags, location?: Node | DocumentPosition, excludeGlobals?: boolean): Symbol | undefined;" },
    { name: "typeToString", text: "typeToString(type: Type, enclosingDeclaration?: Node, flags?: number): string;" },
  ] },
  { owner: "NodeHandle", members: [
    { name: "resolve", text: "resolve(project?: Project): Node | undefined;" },
  ] },
  { owner: "Symbol", members: [
    { name: "declarations", text: "readonly declarations: readonly NodeHandle[];" },
    { name: "flags", text: "readonly flags: SymbolFlags;" },
    { name: "id", text: "readonly id: number;" },
    { name: "name", text: "readonly name: string;" },
    { name: "valueDeclaration", text: "readonly valueDeclaration: NodeHandle | undefined;" },
  ] },
  { owner: "Type", members: [
    { name: "flags", text: "readonly flags: TypeFlags;" },
    { name: "id", text: "readonly id: number;" },
    { name: "getSymbol", text: "getSymbol(): Symbol | undefined;" },
    { name: "getAliasTypeArguments", text: "getAliasTypeArguments(): readonly Type[];" },
    { name: "getAliasSymbol", text: "getAliasSymbol(): Symbol | undefined;" },
    { name: "isErrorType", text: "isErrorType(): boolean;" },
  ] },
  { owner: "Signature", members: [
    { name: "getParameters", text: "getParameters(): readonly Symbol[];" },
    { name: "getTypeParameters", text: "getTypeParameters(): readonly TypeParameter[];" },
    { name: "thisParameter", text: "readonly thisParameter?: number | undefined;" },
  ] },
];

/** The host package's node list interface, read as a dense readonly array of
 * its elements (COMPILER-API.md, "Node lists in the model"), never through
 * its declaration. */
export const hostNodeList = "NodeArray";

/** The reviewed host declarations' digest (C0): the SHA-256 of every
 * `.d.ts` file under the audited installation's `dist/`, each its path from
 * the package root, a NUL, its bytes and a NUL, in path order, after the
 * package's version. A different digest is a different package, refused
 * until the contract is reviewed again. */
export const hostDeclarationsDigest = "16f2260fe0003d51dfb6b8503926ce01ff3e8afd3842a3351d3d544c1e81d492";

/** The digest of the declarations of the package installed at `root`. */
export function declarationsDigest(root: string): string {
  const hash = createHash("sha256");
  const manifest: unknown = JSON.parse(readText(join(root, "package.json")));
  const version = typeof manifest === "object" && manifest !== null && "version" in manifest ? String(manifest.version) : "";
  hash.update(`${version}\0`);
  const files: string[] = [];
  const walk = (directory: string): void => {
    for (const entry of listDirectory(directory)) {
      const path = join(directory, entry.name);
      if (entry.isDirectory()) walk(path);
      else if (entry.name.endsWith(".d.ts")) files.push(relative(root, path).split(sep).join("/"));
    }
  };
  walk(join(root, "dist"));
  for (const file of files.sort()) {
    hash.update(`${file}\0`);
    hash.update(readBytes(join(root, file)));
    hash.update("\0");
  }
  return hash.digest("hex");
}

/** The host installation: the package directory and whether its digest is
 * checked. */
type Installation = { root: string; checked: boolean };

/** The audited installation: the package `typescript` the front end itself
 * resolves (`tools/package-lock.json` pins it), its real path. */
let audited: Installation | null = null;
/** A stand-in installation a test supplies (`useHostInstallationForTests`);
 * no entry point of the pipeline sets it. */
let standIn: Installation | null = null;
let digestChecked: boolean = false;

function installation(): Installation {
  if (standIn) return standIn;
  audited ??= { root: realPath(dirname(resolveModule(import.meta.url, `${hostPackage.name}/package.json`))),
    checked: true };
  return audited;
}

/** Tests only: read the package at `root` as the host package, its digest
 * unchecked, until called again with null. */
export function useHostInstallationForTests(root: string | null): void {
  standIn = root === null ? null : { root: realPath(root), checked: false };
}

/** Whether `file` is a declaration of the host package: a file of the
 * audited installation, whose declarations have the reviewed digest. A
 * package elsewhere, whatever its manifest names, is no host. */
export function isHostFile(file: string): boolean {
  // A path that names nothing is no host file; any other failure resolving
  // it is the tool's.
  const real = orAbsent(realPath, file);
  if (real === null) return false;
  const host = installation();
  if (!real.startsWith(host.root + sep)) return false;
  if (host.checked && !digestChecked) {
    const digest = declarationsDigest(host.root);
    if (digest !== hostDeclarationsDigest)
      throw Error(`the host package at ${host.root} is not the reviewed one: its declarations' digest is ${digest}, ` +
        `the contract was reviewed against ${hostDeclarationsDigest}`);
    digestChecked = true;
  }
  return true;
}

/** A guard table checked against the installation the run admits, once
 * per table (HOST-FAMILIES.md, "The guard table"). Its entry point is
 * re-derived from the package's own manifest under the table's conditions,
 * and its `imports` mappings found as recorded. Each entry's export is
 * resolved as the module linker resolves it, through each module's own
 * exports and its `export *` modules, a name two of those provide being no
 * export, to the function the entry records, of exactly its text and never
 * assigned in its module. Each free name of that function, and of each
 * helper it reaches, is a function of its module or a named import of the
 * package: the helpers and the binding edges this closure reaches are
 * exactly the entry's, each helper of exactly its recorded text and never
 * assigned. `parse` gives a module's tree. A mismatch is no table: every
 * guard of the family is then read without predicate. */
const activeTables = new Map<GuardTable, ReadonlyMap<string, GuardEntry> | null>();
export function activeGuards(table: GuardTable): ReadonlyMap<string, GuardEntry> | null {
  if (activeTables.has(table)) return activeTables.get(table) ?? null;
  const root = installation().root;
  // The package's modules, read by a compiler of the check's own.
  const contents = new Map<string, string>();
  const api = openCompiler({ cwd: root, fs: {
    readFile: (name) => contents.get(name),
    fileExists: (name) => (contents.has(name) ? true : undefined),
  } });
  const parse = (path: string, text: string): ts.SourceFile => {
    contents.set(path, text);
    const file = api.updateSnapshot({ openFiles: [path] }).getDefaultProjectForFile(path)?.program.getSourceFile(path);
    if (!file) throw Error(`the compiler produced no tree for ${path}`);
    return file;
  };
  let result: ReadonlyMap<string, GuardEntry> | null = null;
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
  activeTables.set(table, result);
  return result;
}
function checkedGuards(table: GuardTable, root: string, parse: (path: string, text: string) => ts.SourceFile):
    ReadonlyMap<string, GuardEntry> | null {
  const manifest: unknown = JSON.parse(readText(join(root, "package.json")));
  if (typeof manifest !== "object" || manifest === null || !("exports" in manifest) || !("imports" in manifest)) return null;
  const { exports, imports } = manifest;
  const record = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
  if (!record(exports) || !record(imports)) return null;
  const target = (mapping: unknown): string | null => {
    if (typeof mapping === "string") return mapping;
    if (!record(mapping)) return null;
    for (const [condition, value] of Object.entries(mapping))
      if (table.conditions.includes(condition)) return target(value);
    return null;
  };
  const normal = (path: string): string => relative(root, join(root, path)).split(sep).join("/");
  const entryTarget = target(exports[table.entryPoint]);
  if (!entryTarget || normal(entryTarget) !== table.entryModule) return null;
  for (const [pattern, mapping] of Object.entries(table.imports))
    if (JSON.stringify(imports[pattern]) !== JSON.stringify(mapping)) return null;
  const resolveSpecifier = (from: string, specifier: string): string | null => {
    if (specifier.startsWith("./") || specifier.startsWith("../"))
      return relative(root, join(root, dirname(from), specifier)).split(sep).join("/");
    if (!specifier.startsWith("#")) return null;
    // A specifier through `imports`: the manifest's mapping, which must be
    // one the table records.
    for (const [pattern, mapping] of Object.entries(imports)) {
      const star = pattern.indexOf("*");
      const matches = pattern === specifier || (star >= 0 && specifier.startsWith(pattern.slice(0, star)) &&
        specifier.endsWith(pattern.slice(star + 1)) && specifier.length >= pattern.length - 1);
      if (!matches) continue;
      if (!(pattern in table.imports)) return null;
      const to = target(mapping);
      if (!to) return null;
      return star >= 0 ? normal(to.replace("*", specifier.slice(star, specifier.length - (pattern.length - star - 1)))) : normal(to);
    }
    return null;
  };
  const trees = new Map<string, ts.SourceFile>();
  const tree = (module: string): ts.SourceFile => {
    const known = trees.get(module);
    if (known) return known;
    const parsed = parse(join(root, module), readText(join(root, module)));
    trees.set(module, parsed);
    return parsed;
  };
  const exported = (s: ts.Statement): boolean =>
    (ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s) || ts.isVariableStatement(s)) &&
    (s.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) ?? false);
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
  // What the export `name` of a module resolves to, as the linker resolves
  // it: the module's own export, else the one export of its `export *`
  // modules that provides it; the modules passed through, in order.
  type Resolved = { module: string; local: string; path: string[] };
  const resolveExport = (module: string, name: string, seen: readonly string[]): Resolved | "ambiguous" | null => {
    if (seen.includes(module)) return null;
    const here = [...seen, module];
    const file = tree(module);
    for (const s of file.statements) {
      if (exported(s) && (ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && s.name?.text === name)
        return { module, local: name, path: here };
      if (exported(s) && ts.isVariableStatement(s) &&
          s.declarationList.declarations.some(d => ts.isIdentifier(d.name) && d.name.text === name))
        return { module, local: name, path: here };
      if (ts.isExportDeclaration(s) && s.exportClause && ts.isNamedExports(s.exportClause))
        for (const e of s.exportClause.elements)
          if (e.name.text === name) {
            const local = e.propertyName ? e.propertyName.getText(file) : e.name.text;
            if (!s.moduleSpecifier) return { module, local, path: here };
            const next = ts.isStringLiteral(s.moduleSpecifier) ? resolveSpecifier(module, s.moduleSpecifier.text) : null;
            return next ? resolveExport(next, local, here) : null;
          }
      if (ts.isExportDeclaration(s) && s.exportClause && ts.isNamespaceExport(s.exportClause) &&
          s.exportClause.name.getText(file) === name) return null;
    }
    const found: Resolved[] = [];
    for (const s of file.statements)
      if (ts.isExportDeclaration(s) && !s.exportClause && s.moduleSpecifier && ts.isStringLiteral(s.moduleSpecifier)) {
        const next = resolveSpecifier(module, s.moduleSpecifier.text);
        if (!next) return null;
        const r = resolveExport(next, name, here);
        if (r === "ambiguous") return r;
        if (r && !found.some(f => f.module === r.module && f.local === r.local)) found.push(r);
      }
    const [one] = found;
    return found.length > 1 ? "ambiguous" : one ?? null;
  };
  // A module's named imports: each local name, the module it resolves to
  // and the name it imports.
  const importsOf = (module: string): Map<string, { module: string; name: string }> => {
    const out = new Map<string, { module: string; name: string }>();
    for (const s of tree(module).statements) {
      if (!ts.isImportDeclaration(s) || !ts.isStringLiteral(s.moduleSpecifier)) continue;
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
  const entries = new Map<string, GuardEntry>();
  for (const entry of table.guards) {
    const resolved = resolveExport(table.entryModule, entry.name, []);
    if (!resolved || resolved === "ambiguous" || resolved.module !== entry.module || resolved.local !== entry.name ||
        resolved.path.join("\n") !== entry.chain.join("\n")) return null;
    const f = functionOf(entry.module, entry.name);
    if (!f || textOf(entry.module, f) !== entry.text) return null;
    // The dependency closure: helpers and binding edges reached.
    const helpers = new Set<string>();
    const edges = new Set<string>();
    const pending: { module: string; f: ts.FunctionDeclaration }[] = [{ module: entry.module, f }];
    for (let next = pending.pop(); next; next = pending.pop()) {
      const { module } = next;
      for (const name of freeNames(next.f)) {
        const local = functionOf(module, name);
        const imported = importsOf(module).get(name);
        if (local) {
          const key = `${module}#${name}`;
          if (table.helpers[key] !== textOf(module, local)) return null;
          if (!helpers.has(key)) { helpers.add(key); pending.push({ module, f: local }); }
        } else if (imported) {
          edges.add(JSON.stringify([name, imported.module]));
          const helper = functionOf(imported.module, imported.name);
          if (helper) {
            const key = `${imported.module}#${imported.name}`;
            if (table.helpers[key] !== textOf(imported.module, helper)) return null;
            if (!helpers.has(key)) { helpers.add(key); pending.push({ module: imported.module, f: helper }); }
          }
        } else return null;
      }
    }
    const recordedEdges = new Set(entry.edges.map(e => JSON.stringify(e)));
    if (helpers.size !== entry.helpers.length || !entry.helpers.every(h => helpers.has(h)) ||
        edges.size !== recordedEdges.size || ![...edges].every(e => recordedEdges.has(e))) return null;
    entries.set(entry.name, entry);
  }
  return entries;
}

/** The entry of the compiler API's family guarding a declaration: the
 * function `name` of the declaration file `file`, which the entry's module
 * declares. */
export function guardEntry(file: string, name: string): GuardEntry | null {
  if (!isHostFile(file)) return null;
  const entries = activeGuards(hostFamily().guards);
  const entry = entries?.get(name);
  if (!entry) return null;
  const declared = relative(installation().root, realPath(file)).split(sep).join("/");
  return declared === entry.module.replace(/\.js$/, ".d.ts") ? entry : null;
}
