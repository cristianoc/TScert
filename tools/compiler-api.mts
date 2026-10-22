/** The compiler API as a host library (COMPILER-API.md): the reviewed
 * contract under which code reading TypeScript's trees and checker through
 * the package `typescript` is verified.
 *
 * The package's declarations are read on use, by the declaration reader's
 * rules for host declarations; this file states what a declaration cannot:
 * which package is the host, and which of its enums the contract reads as
 * values. Each entry is checked against the installed package by
 * `tests/compiler-api.mts`. */
import type { DeclarationIdentity, TypeTerm } from "./declaration-types.mts";
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
];

/** The entry points whose enum exports C1 compares with the audited objects.
 * Binding recognition resolves imports to these modules through Node. */
export const hostEnumModules: readonly { specifier: string; namespace: Readonly<Record<string, unknown>> }[] = [
  { specifier: "typescript/unstable/ast", namespace: ts },
  { specifier: "typescript/unstable/sync", namespace: sync },
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
  // Every property member of a shape, required or optional, is stable
  // (reading rule 1, checked by C3's walk).
  stable: { excluded: [] },
  guards: compilerApiGuards,
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
    { name: "getTypePredicateOfSignature", text: "getTypePredicateOfSignature(signature: Signature): TypePredicate | undefined;" },
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
    { name: "getThisParameter", text: "getThisParameter(): Symbol | undefined;" },
    { name: "getTypeParameters", text: "getTypeParameters(): readonly TypeParameter[];" },
    { name: "thisParameter", text: "readonly thisParameter?: number | undefined;" },
  ] },
];

/** The host package's node list interface, read as a dense readonly array of
 * its elements (COMPILER-API.md, "Node lists in the model"), never through
 * its declaration. */
export const hostNodeList = "NodeArray";
