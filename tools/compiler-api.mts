/** The compiler API as a host library (COMPILER-API.md): the reviewed
 * contract under which code reading TypeScript's trees and checker through
 * the package `typescript` is verified.
 *
 * The package's declarations are read on use, by the declaration reader's
 * rules for host declarations; this file states what a declaration cannot:
 * which package is the host, and which of its enums the contract reads as
 * values. Each entry is checked against the installed package by
 * `tests/compiler-api.mts`. */
import type { CallEffect, DeclarationIdentity, TypeTerm } from "./declaration-types.mts";
import type { FamilyDescription } from "./host-families.mts";
import { compilerApiGuards } from "./compiler-api-guards.mts";
import * as ts from "typescript/unstable/ast";
import * as sync from "typescript/unstable/sync";
import type { Node } from "typescript/unstable/ast";
import { nameOf } from "./syntax.mts";

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
  { name: "TypePredicateKind", file: "typePredicateKind" },
];

/** The entry points whose enum exports C1 compares with the audited objects,
 * each with its exports by name. Binding recognition resolves imports to
 * these modules through Node. */
export const hostEnumModules: readonly { specifier: string; namespace: ReadonlyMap<string, unknown> }[] = [
  { specifier: "typescript/unstable/ast", namespace: new Map(Object.entries(ts)) },
  { specifier: "typescript/unstable/sync", namespace: new Map(Object.entries(sync)) },
];

/** The compiler API's family description (HOST-FAMILIES.md, "The compiler
 * API"): the syntax tree's nodes, tagged by `kind`. The generic rule names
 * every generic node declaration; `KeywordExpression` gives the shapes of
 * `null`, `true`, `false`, `this`, `super` and `import`, which the
 * declarations make expressions. Each correction is a field the
 * declarations state required and the runtime leaves absent (COMPILER-API.md,
 * "Corrections"). */
export const compilerApiFamily: FamilyDescription = {
  package: hostPackage,
  // The installation the tools themselves resolve (`tools/package-lock.json`
  // pins it), and its declarations' digest (C0).
  installation: { from: "tools", digest: "d4dd6af2e526953d47e88c50064e92375286e4ac30c9dfa80f9edff1d0954a9a" },
  marker: "RemoteNode",
  root: { name: "Node", form: "inheritance", text: "export interface Node extends ReadonlyTextRange {" },
  tag: { field: "kind", primitive: "number", constants: { enum: "SyntaxKind" } },
  table: [
    { rule: "literal" },
    // A JavaScript file's JSDoc `@typedef` or `@callback`, which the parser
    // reparses into a statement of kind `JSTypeAliasDeclaration` (345), of
    // its file's or its block's `statements`, and which no declaration
    // states (COMPILER-API.md, "Audited shapes"). Its runtime object is a
    // `RemoteNode`, whose child getters read through the kind's child list
    // (`node.generated.js:293-304`); the list of 345 is
    // `TypeAliasDeclaration`'s, `modifiers`, `name`, `typeParameters` and
    // `type` (`protocol.generated.js:40-41`), and `modifierFlags` and `flags`
    // are computed from them and the node's record (`node.generated.js:821-833`)
    // as for every kind. So it has `TypeAliasDeclaration`'s members at its own
    // kind, and is a statement and a declaration as that one is.
    { rule: "audited", shapes: [
      { kind: "JSTypeAliasDeclaration", bases: ["DeclarationBase", "StatementBase", "ModifiersBase"], members: [
        { owner: "TypeAliasDeclaration", member: "name", text: "readonly name: Identifier;" },
        { owner: "TypeAliasDeclaration", member: "typeParameters", text: "readonly typeParameters?: NodeArray<TypeParameterDeclaration>;" },
        { owner: "TypeAliasDeclaration", member: "type", text: "readonly type: TypeNode;" },
      ] },
      // A JavaScript file's JSDoc `@import`, which the parser reparses into
      // a statement of kind `JSImportDeclaration` (346), and which no
      // declaration states (COMPILER-API.md, "Audited shapes"). Its child
      // list is `ImportDeclaration`'s, `modifiers`, `importClause`,
      // `moduleSpecifier` and `attributes` (`protocol.generated.js:45-46`),
      // read through the same getters (`node.generated.js:293-304`); the server
      // at the package's revision builds it from the clause, specifier and
      // attributes of the tag, parsed as kind 273's are, the specifier always
      // present (COMPILER-API.md, "Audited shapes", the audit). So it
      // has `ImportDeclaration`'s members at its own kind, and is a
      // statement and a declaration as that one is.
      { kind: "JSImportDeclaration", bases: ["DeclarationBase", "StatementBase", "ModifiersBase"], members: [
        { owner: "ImportDeclaration", member: "importClause", text: "readonly importClause?: ImportClause;" },
        { owner: "ImportDeclaration", member: "moduleSpecifier", text: "readonly moduleSpecifier: Expression;" },
        { owner: "ImportDeclaration", member: "attributes", text: "readonly attributes?: ImportAttributes;" },
      ] },
    ] },
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
  // The members of host types whose reads give no one value for a node's
  // life (reading rule 1): `jsDoc` builds a fresh array on each read
  // (`node.generated.js:221`); `SourceFile.tokenCache`, which no getter
  // backs, the entry point's own token functions assign on the file they are
  // given (`astnav.js:510-513`, `getOrCreateToken`), absent before and a
  // `Map` after. The declaration reader omits each from every shape, so every
  // read of it is a read of a member the type does not state.
  omitted: [
    { owner: "Node", member: "jsDoc", text: "readonly jsDoc?: readonly Node[] | undefined;", why: "allocates" },
    { owner: "SourceFile", member: "tokenCache", text: "tokenCache?: Map<string, Node>;", why: "assigned" },
  ],
  // The callback-free node methods (T3, COMPILER-API.md, "Node methods and
  // callbacks"): they make no server request, run no client code and change
  // no stable member, and their hidden effects (a node list's cursor, the
  // file's materialized nodes) are observed by no transparent operation
  // (T4), so a call changes no location of the model, on normal return or
  // throw. `forEachChild`'s own steps change none either and the only client
  // code it runs is its visitors, synchronously, each passed a child of the
  // receiver in a fixed order, a throw propagating (T3): with both visitors
  // within a closed footprint, its call is within it on normal return
  // (COMPILER-API.md, "Node methods and callbacks").
  footprints: [
    { owner: "Node", member: "forEachChild",
      text: "forEachChild<T>(visitor: (node: Node) => T, visitArray?: (nodes: NodeArray<Node>) => T): T | undefined;",
      kind: "callbacks" },
    { owner: "Node", member: "getSourceFile", text: "getSourceFile(): SourceFile;", kind: "empty" },
    { owner: "Node", member: "getStart", text: "getStart(sourceFile?: SourceFile, includeJsDocComment?: boolean): number;", kind: "empty" },
    { owner: "Node", member: "getFullStart", text: "getFullStart(): number;", kind: "empty" },
    { owner: "Node", member: "getEnd", text: "getEnd(): number;", kind: "empty" },
    { owner: "Node", member: "getWidth", text: "getWidth(sourceFile?: SourceFile): number;", kind: "empty" },
    { owner: "Node", member: "getFullWidth", text: "getFullWidth(): number;", kind: "empty" },
    { owner: "Node", member: "getLeadingTriviaWidth", text: "getLeadingTriviaWidth(sourceFile?: SourceFile): number;", kind: "empty" },
    { owner: "Node", member: "getFullText", text: "getFullText(sourceFile?: SourceFile): string;", kind: "empty" },
    { owner: "Node", member: "getText", text: "getText(sourceFile?: SourceFile): string;", kind: "empty" },
    { owner: "SourceFile", member: "getLineAndCharacterOfPosition",
      text: "getLineAndCharacterOfPosition(position: number): LineAndCharacter;", kind: "empty" },
  ],
  // Every property member of a shape, required or optional, is stable
  // (reading rule 1, checked by C3's walk).
  stable: { excluded: [] },
  guards: compilerApiGuards,
  // The node guards' behaviour on `undefined`, audited per entry: each reads
  // the tag first and throws a `TypeError` (COMPILER-API.md, "Guards").
  undefinedInputs: ["node"],
};

/** The package's node builders (COMPILER-API.md, R2): the declaration
 * files, by their path in the installation, of the functions the admitted
 * entry point exports that return nodes they build, outside the node
 * invariant: the factory's `NodeObject` starts with no `parent`
 * (`factory.generated.js:13`), and a clone's or a visitor's root keeps none
 * (`clone.js:56-78`, `visitor.generated.js`). The handwritten JSDoc
 * parameter/property visitors (`visitor.js`) call factory updates whose
 * replacement roots likewise lack `parent`. No value they declare is read. */
export const hostNodeBuilders: readonly string[] = [
  "dist/ast/factory.generated.d.ts",
  "dist/ast/clone.d.ts",
  "dist/ast/visitor.generated.d.ts",
  "dist/ast/visitor.d.ts",
];

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

/** A brand lookup preserves existing array prefixes on normal return. */
export type BrandPredicate = (id: DeclarationIdentity) => Within<{ value: "any"; store: "grow" }, boolean>;

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
export function hostBrands(t: TypeTerm, out: boolean | null, brand: BrandPredicate,
    fail: (message: string) => never): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const go = (u: TypeTerm, o: boolean | null): Within<{ value: "any"; store: "grow" }, TypeTerm> => hostBrands(u, o, brand, fail);
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
    brand: BrandPredicate, fail: (message: string) => never): Within<{ value: "any"; store: "grow" }, Extract<TypeTerm, { k: "constructor" }>> {
  const flip = out === null ? null : !out;
  const go = (u: TypeTerm, o: boolean | null): Within<{ value: "any"; store: "grow" }, TypeTerm> => hostBrands(u, o, brand, fail);
  return { ...t, params: t.params.map(p => go(p, flip)), rest: t.rest && go(t.rest, flip), result: go(t.result, out),
    ...(t.statics ? { statics: t.statics.map(s => ({ ...s, type: go(s.type, s.readonly ? out : null) })) } : {}) };
}
function hostBrandsFunction(t: Extract<TypeTerm, { k: "function" }>, out: boolean | null,
    brand: BrandPredicate, fail: (message: string) => never): Within<{ value: "any"; store: "grow" }, Extract<TypeTerm, { k: "function" }>> {
  const flip = out === null ? null : !out;
  const go = (u: TypeTerm, o: boolean | null): Within<{ value: "any"; store: "grow" }, TypeTerm> => hostBrands(u, o, brand, fail);
  return { ...t, receiver: t.receiver && go(t.receiver, flip), params: t.params.map(p => go(p, flip)),
    rest: t.rest && go(t.rest, flip), result: go(t.result, out) };
}

/** The named views of the host classes (reading rule 4): each class is read
 * through the members its view lists, each read exactly as its reviewed
 * declaration text states it; an overloaded member is the overloads listed.
 * An entry marked `fresh` returns an array its call allocates (audited,
 * COMPILER-API.md, "Audits of sync members"), which its request reading
 * states (`requestReading`). An entry marked `request` carries the audited
 * normal-return store-growth effect. An entry marked `table` returns a native `Map`
 * whose keys are strings the package produced (audited, COMPILER-API.md,
 * "Audits of sync members"), which `tableReading` reads at `string` keys.
 * A class the contract lists no view for has none: no member. The members
 * are the ones the front end reads (2026-10-29), but `Type`'s `this is X`
 * methods, whose promise is about the receiver, which is no actual of a call:
 * the stated guards of their names state them as functions (`statedGuards`).
 * `Type`, an interface, has a view of its own as a class does. */
export const hostViews: readonly { owner: string; members: readonly { name: string; text: string; request?: true; fresh?: true; table?: true }[] }[] = [
  { owner: "API", members: [
    { name: "parseConfigFile", text: "parseConfigFile(file: DocumentIdentifier): ConfigResponse;" },
    { name: "close", request: true, text: "close(): void;" },
    { name: "updateSnapshot", text: "updateSnapshot(params?: FromLSP extends true ? LSPUpdateSnapshotParams : UpdateSnapshotParams): Snapshot;" },
  ] },
  { owner: "Snapshot", members: [
    { name: "getProjects", request: true, text: "getProjects(): readonly Project[];" },
    { name: "dispose", request: true, text: "dispose(): void;" },
    { name: "getDefaultProjectForFile", text: "getDefaultProjectForFile(file: DocumentIdentifier): Project | undefined;" },
    { name: "getProject", request: true, text: "getProject(configFileName: string): Project | undefined;" },
  ] },
  { owner: "Project", members: [
    { name: "checker", text: "readonly checker: Checker;" },
    { name: "compilerOptions", text: "readonly compilerOptions: CompilerOptions;" },
    { name: "configFileName", text: "readonly configFileName: string;" },
    { name: "program", text: "readonly program: Program;" },
    { name: "rootFiles", text: "readonly rootFiles: readonly string[];" },
  ] },
  { owner: "Program", members: [
    { name: "getDeclarationDiagnostics", text: "getDeclarationDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];" },
    { name: "getGlobalDiagnostics", request: true, text: "getGlobalDiagnostics(): readonly Diagnostic[];" },
    { name: "getProgramDiagnostics", request: true, text: "getProgramDiagnostics(): readonly Diagnostic[];" },
    { name: "getSemanticDiagnostics", text: "getSemanticDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];" },
    { name: "getSourceFile", text: "getSourceFile(file: DocumentIdentifier): SourceFile | undefined;" },
    { name: "getSourceFileNames", request: true, text: "getSourceFileNames(): readonly string[];" },
    { name: "getSyntacticDiagnostics", text: "getSyntacticDiagnostics(file?: DocumentIdentifier): readonly Diagnostic[];" },
    { name: "isSourceFileDefaultLibrary", request: true, text: "isSourceFileDefaultLibrary(file: SourceFile): boolean;" },
  ] },
  { owner: "Checker", members: [
    { name: "getContextualType", request: true, text: "getContextualType(node: Expression): Type | undefined;" },
    { name: "getAliasedSymbol", request: true, text: "getAliasedSymbol(symbol: Symbol): Symbol;" },
    { name: "getConstantValue", request: true, text: "getConstantValue(node: Node): string | number | undefined;" },
    { name: "getExportsOfModule", request: true, text: "getExportsOfModule(symbol: Symbol): readonly Symbol[];" },
    { name: "getImmediateAliasedSymbol", request: true, text: "getImmediateAliasedSymbol(symbol: Symbol): Symbol | undefined;" },
    { name: "getIndexInfosOfType", request: true, text: "getIndexInfosOfType(type: Type): readonly IndexInfo[];" },
    { name: "getNonNullableType", request: true, text: "getNonNullableType(type: Type): Type | undefined;" },
    { name: "getParameterType", request: true, text: "getParameterType(signature: Signature, index: number): Type | undefined;" },
    { name: "getPropertiesOfType", request: true, text: "getPropertiesOfType(type: Type): readonly Symbol[];" },
    { name: "getPropertyOfType", request: true, text: "getPropertyOfType(type: Type, name: string): Symbol | undefined;" },
    { name: "getResolvedSignature", request: true, text: "getResolvedSignature(node: Node): Signature | undefined;" },
    { name: "getReturnTypeOfSignature", request: true, text: "getReturnTypeOfSignature(signature: Signature): Type | undefined;" },
    { name: "getShorthandAssignmentValueSymbol", request: true, text: "getShorthandAssignmentValueSymbol(node: Node): Symbol | undefined;" },
    { name: "getSignaturesOfType", request: true, text: "getSignaturesOfType(type: Type, kind: SignatureKind): readonly Signature[];" },
    { name: "getSymbolAtLocation", request: true, text: "getSymbolAtLocation(node: Node): Symbol | undefined;" },
    { name: "getSymbolAtLocation", request: true, text: "getSymbolAtLocation(nodes: readonly Node[]): (Symbol | undefined)[];", fresh: true },
    { name: "getTypeArguments", request: true, text: "getTypeArguments(type: TypeReference): readonly Type[];" },
    { name: "getTypeAtLocation", request: true, text: "getTypeAtLocation(node: Node): Type | undefined;" },
    { name: "getTypeAtLocation", request: true, text: "getTypeAtLocation(nodes: readonly Node[]): (Type | undefined)[];", fresh: true },
    { name: "getTypeFromTypeNode", request: true, text: "getTypeFromTypeNode(node: TypeNode): Type | undefined;" },
    { name: "getTypeOfSymbol", request: true, text: "getTypeOfSymbol(symbol: Symbol): Type | undefined;" },
    { name: "getTypePredicateOfSignature", request: true, text: "getTypePredicateOfSignature(signature: Signature): TypePredicate | undefined;" },
    { name: "isArrayType", request: true, text: "isArrayType(type: Type): boolean;" },
    { name: "isTupleType", request: true, text: "isTupleType(type: Type): boolean;" },
    { name: "isUndefinedSymbol", request: true, text: "isUndefinedSymbol(symbol: Symbol): boolean;" },
    { name: "isUnknownSymbol", request: true, text: "isUnknownSymbol(symbol: Symbol): boolean;" },
    { name: "resolveName", text: "resolveName(name: string, meaning: SymbolFlags, location?: Node | DocumentPosition, excludeGlobals?: boolean): Symbol | undefined;" },
    { name: "typeToString", request: true, text: "typeToString(type: Type, enclosingDeclaration?: Node, flags?: number): string;" },
  ] },
  { owner: "NodeHandle", members: [
    { name: "resolve", request: true, text: "resolve(project?: Project): Node | undefined;" },
  ] },
  { owner: "Symbol", members: [
    { name: "checkFlags", text: "readonly checkFlags: number;" },
    { name: "declarations", text: "readonly declarations: readonly NodeHandle[];" },
    { name: "flags", text: "readonly flags: SymbolFlags;" },
    { name: "id", text: "readonly id: number;" },
    { name: "name", text: "readonly name: string;" },
    { name: "valueDeclaration", text: "readonly valueDeclaration: NodeHandle | undefined;" },
    { name: "getMembers", request: true, text: "getMembers(): ReadonlyMap<__String, Symbol>;", table: true },
    { name: "getExports", request: true, text: "getExports(): ReadonlyMap<__String, Symbol>;", table: true },
  ] },
  { owner: "Type", members: [
    { name: "flags", text: "readonly flags: TypeFlags;" },
    { name: "id", text: "readonly id: number;" },
    { name: "getSymbol", request: true, text: "getSymbol(): Symbol | undefined;" },
    { name: "getAliasTypeArguments", request: true, text: "getAliasTypeArguments(): readonly Type[];" },
    { name: "getAliasSymbol", request: true, text: "getAliasSymbol(): Symbol | undefined;" },
    { name: "isErrorType", request: true, text: "isErrorType(): boolean;" },
  ] },
  // The predicates about `this` (COMPILER-API.md, "Audits of sync members"):
  // the client copies the server's `parameterIndex`, 0 for them, where the
  // declarations state `undefined`, so their views state no index.
  { owner: "ThisTypePredicate", members: [
    { name: "kind", text: "readonly kind: TypePredicateKind.This;" },
    { name: "parameterName", text: "readonly parameterName: undefined;" },
    { name: "type", text: "readonly type: Type;" },
  ] },
  { owner: "AssertsThisTypePredicate", members: [
    { name: "kind", text: "readonly kind: TypePredicateKind.AssertsThis;" },
    { name: "parameterName", text: "readonly parameterName: undefined;" },
    { name: "type", text: "readonly type: Type | undefined;" },
  ] },
  { owner: "Signature", members: [
    { name: "declaration", text: "readonly declaration?: NodeHandle | undefined;" },
    { name: "getParameters", request: true, text: "getParameters(): readonly Symbol[];" },
    { name: "getThisParameter", request: true, text: "getThisParameter(): Symbol | undefined;" },
    { name: "getTypeParameters", request: true, text: "getTypeParameters(): readonly TypeParameter[];" },
    { name: "thisParameter", text: "readonly thisParameter?: number | undefined;" },
  ] },
];

/** The stated type guards (T7, COMPILER-API.md, "Stated type guards"): the
 * sync API's predicates over `Type` a unit narrows by, each read at its
 * reviewed declaration (`dist/api/sync/api.d.ts`), its plain signature and
 * its promise about its argument, both changing no value and no store. Its
 * implementation (`dist/api/sync/api.js`), which `tests/compiler-api.mts`
 * compares with the function Node loads, reads its argument's own data
 * field `flags` (`isTypeReference`, through the module's `isObjectType`,
 * also `objectFlags`) and the enum objects C1 checks, and nothing else: on a
 * host `Type`, a `TypeObject` whose prototype defines no accessor, it runs
 * no code of the program, makes no request, writes nothing and throws
 * nothing. Its promise is T7: on a value of a host type
 * it returns `true` for, the members the promised interface adds over `Type`
 * return values of their declared types. The `this is X` methods of `Type`
 * calling them are outside the fragment (`invalid-compiler-api-type-method`). */
export const statedGuards: readonly { name: string; text: string; implementation: string }[] = [
  { name: "isUnionType", text: "export declare function isUnionType(type: Type): type is UnionType;",
    implementation: "function isUnionType(type) {\n    return (type.flags & TypeFlags.Union) !== 0;\n}" },
  { name: "isIntersectionType", text: "export declare function isIntersectionType(type: Type): type is IntersectionType;",
    implementation: "function isIntersectionType(type) {\n    return (type.flags & TypeFlags.Intersection) !== 0;\n}" },
  { name: "isStringLiteralType", text: "export declare function isStringLiteralType(type: Type): type is StringLiteralType;",
    implementation: "function isStringLiteralType(type) {\n    return (type.flags & TypeFlags.StringLiteral) !== 0;\n}" },
  { name: "isNumberLiteralType", text: "export declare function isNumberLiteralType(type: Type): type is NumberLiteralType;",
    implementation: "function isNumberLiteralType(type) {\n    return (type.flags & TypeFlags.NumberLiteral) !== 0;\n}" },
  { name: "isBigIntLiteralType", text: "export declare function isBigIntLiteralType(type: Type): type is BigIntLiteralType;",
    implementation: "function isBigIntLiteralType(type) {\n    return (type.flags & TypeFlags.BigIntLiteral) !== 0;\n}" },
  { name: "isBooleanLiteralType", text: "export declare function isBooleanLiteralType(type: Type): type is BooleanLiteralType;",
    implementation: "function isBooleanLiteralType(type) {\n    return (type.flags & TypeFlags.BooleanLiteral) !== 0;\n}" },
  { name: "isTypeReference", text: "export declare function isTypeReference(type: Type): type is TypeReference;",
    implementation: "function isTypeReference(type) {\n    return isObjectType(type) && (type.objectFlags & ObjectFlags.Reference) !== 0;\n}" },
];

/** The reading of a view member explicitly marked `request`: each signature
 * at `{value: any, store: grow}`, on normal return only. An unmarked member
 * retains its declared effects, including methods whose serialization runs
 * getters or `toJSON` of program objects. A `fresh` entry additionally states
 * that an array result's store is allocated by the call. */
export function requestReading(type: TypeTerm, fresh: boolean): TypeTerm {
  const effect: CallEffect = { footprint: { value: "any", store: "grow" }, promise: null, fresh: false,
    receiverStore: false, onThrow: false, receiverOwn: false, freshObject: false, requires: null, elements: null, pre: [] };
  const at = (t: TypeTerm): TypeTerm =>
    t.k === "function" && t.effect.promise === null
      ? { ...t, effect: { footprint: effect.footprint, promise: effect.promise, fresh: fresh && t.result.k === "array",
        receiverStore: effect.receiverStore, onThrow: effect.onThrow, receiverOwn: effect.receiverOwn,
        freshObject: effect.freshObject, requires: effect.requires, elements: effect.elements, pre: effect.pre } }
    : t.k === "intersection" ? { ...t, parts: t.parts.map(at) }
    : t.k === "scheme" ? { ...t, signatures: t.signatures.map(s => s.k === "function" && s.effect.promise === null ? { ...s, effect } : s) }
    : t;
  return at(type);
}

/** A symbol table's reading (COMPILER-API.md, "Audits of sync members"):
 * a `table` member's signature `(): ReadonlyMap<K, V>`, `K` a branded
 * string, read with `string` at `K`. Its result is a native `Map` the
 * package filled with strings it produced at its keys, so a key it gives is
 * a string (reading rule 5), and `get` and `has`, the standard `Map`
 * methods, take any key: a string the client produces reads the entry the
 * map stores or nothing. Any other signature is refused. */
export function tableReading(type: TypeTerm, isLibraryMap: (id: DeclarationIdentity) => Within<{ value: "keep"; store: "keep" }, boolean>,
    brand: (id: DeclarationIdentity) => boolean, fail: (message: string) => never): TypeTerm {
  if (type.k !== "function" || type.params.length || type.rest || type.result.k !== "reference" ||
      !isLibraryMap(type.result.reference.target) || type.result.args.length !== 2)
    return fail("a symbol table's signature is not `(): ReadonlyMap<K, V>`");
  const [key, value] = type.result.args;
  if (!key || !value || key.k !== "reference" || !brand(key.reference.target))
    return fail("a symbol table's key is no branded string of the package");
  return { ...type, result: { ...type.result, args: [{ k: "atom", name: "string", span: key.span }, value] } };
}

/** The audited implementations of the symbol tables and the type predicate
 * (COMPILER-API.md, "Audits of sync members"), each a method of the sync
 * API's class `owner` (`SnapshotObjectRegistry`, the symbols' registry, is
 * no export) as Node loads it, which C7 compares with the method's text. */
export const auditedSyncMethods: readonly { owner: "Symbol" | "Checker" | "SnapshotObjectRegistry"; name: string; implementation: string }[] = [
  { owner: "Symbol", name: "getMembers",
    implementation: "getMembers() {\n        return this.membersCache ??= this.fetchSymbolTable(\"getMembersOfSymbol\");\n    }" },
  { owner: "Symbol", name: "getExports",
    implementation: "getExports() {\n        return this.exportsCache ??= this.fetchSymbolTable(\"getExportsOfSymbol\");\n    }" },
  { owner: "Symbol", name: "fetchSymbolTable",
    implementation: "fetchSymbolTable(method) {\n        const symbols = this.objectRegistry.fetchSymbols(this, method, undefined, this.canonicalProject.id);\n        const table = new Map();\n        for (const symbol of symbols) {\n            table.set(symbol.escapedName, symbol);\n        }\n        return table;\n    }" },
  { owner: "SnapshotObjectRegistry", name: "fetchSymbols",
    implementation: "fetchSymbols(source, method, handles, projectId) {\n        if (handles) {\n            const result = new Array(handles.length);\n            let allCached = true;\n            for (let i = 0; i < handles.length; i++) {\n                const cached = this.getSymbol(handles[i]);\n                if (!cached) {\n                    allCached = false;\n                    break;\n                }\n                result[i] = cached;\n            }\n            if (allCached)\n                return result;\n        }\n        const symbolData = this.client.apiRequest(method, {\n            snapshot: this.snapshotId,\n            project: projectId,\n            objectId: source.id,\n        });\n        if (symbolData == null)\n            return [];\n        else\n            return symbolData.map(data => this.getOrCreateSymbol(data));\n    }" },
  { owner: "Checker", name: "getTypePredicateOfSignature",
    implementation: "getTypePredicateOfSignature(signature) {\n        const data = this.client.apiRequest(\"getTypePredicateOfSignature\", {\n            snapshot: this.snapshotId,\n            project: this.project.id,\n            signature: signature.id,\n        });\n        if (!data)\n            return undefined;\n        return {\n            kind: data.kind,\n            parameterIndex: data.parameterIndex,\n            parameterName: data.parameterName,\n            type: data.type ? this.objectRegistry.getOrCreateType(data.type) : undefined,\n        };\n    }" },
];

/** The host package's node list interface, read as a dense readonly array of
 * its elements with the members `hostNodeListMembers` states
 * (COMPILER-API.md, "Node lists in the model"), never through its
 * declaration. */
export const hostNodeList = "NodeArray";

/** A node list's own members (COMPILER-API.md, "Node lists"; T4): each with
 * the declaration that states it, as reviewed (`owner` the interface
 * declaring it, `text` its declaration), what backs it on a
 * `RemoteNodeList` (a prototype getter reading the list's buffer, or an own
 * data field the constructor initializes and nothing writes), and the
 * contract the model reads it at, readonly. `hasTrailingComma`, declared
 * optional, is an own data field holding `undefined` on every list: it is
 * read as present, at `boolean | undefined`. */
export const hostNodeListMembers: readonly { name: string; owner: string; text: string;
    backing: "getter" | "field"; contract: "number" | "boolean | undefined" }[] = [
  { name: "pos", owner: "ReadonlyTextRange", text: "readonly pos: number;", backing: "getter", contract: "number" },
  { name: "end", owner: "ReadonlyTextRange", text: "readonly end: number;", backing: "getter", contract: "number" },
  { name: "hasTrailingComma", owner: "NodeArray", text: "hasTrailingComma?: boolean;", backing: "field", contract: "boolean | undefined" },
  { name: "transformFlags", owner: "NodeArray", text: "transformFlags: number;", backing: "field", contract: "number" },
];

/** The record of a node list's own members, each a required readonly field
 * at its contract, located at `span`: the model's node list is the dense
 * readonly array of its elements met with this record. */
export function nodeListMembers(span: TypeTerm["span"]): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const atom = (name: "number" | "boolean" | "undefined"): TypeTerm => ({ k: "atom", name, span });
  return { k: "object", stringIndex: null, calls: [], span, fields: hostNodeListMembers.map(m => ({
    name: m.name, optional: false, readonly: true, span,
    type: m.contract === "number" ? atom("number")
      : { k: "union", parts: [atom("boolean"), atom("undefined")], span } })) };
}
