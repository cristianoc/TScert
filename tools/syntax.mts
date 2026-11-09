/* Optional syntax children read through the declared kinds of compiler
 * nodes. The shared RemoteNode getters select children from each kind
 * list; the guards retain the types of those declared fields.
 */
import * as ts from "typescript/unstable/ast";
import type { ImportDeclaration, Node, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";

/** The compiler's syntax module as the front end resolves it, for the suites
 * outside tools/ that read trees (tests/host-families.mts). */
export * as syntax from "typescript/unstable/ast";
/** The compiler's sync API as the front end resolves it, for the suites
 * outside tools/ that call it (tests/compiler-api.mts). */
export * as sync from "typescript/unstable/sync";

/** The children a node's kinds may carry, by the field that holds them. */
type Child = "name" | "propertyName" | "label" | "type" | "questionToken" | "postfixToken";
type Children = "modifiers" | "typeParameters" | "parameters";

/** One child of `node`, where its kind carries it and it is present. */
export function childOf(node: Node, key: Child): Modifies<{}, Node | undefined> {
  switch (key) {
    case "name":
      if (ts.isVariableDeclaration(node)) return node.name;
      if (ts.isParameterDeclaration(node)) return node.name;
      if (ts.isBindingElement(node)) return node.name;
      if (ts.isFunctionDeclaration(node)) return node.name;
      if (ts.isClassDeclaration(node)) return node.name;
      if (ts.isClassExpression(node)) return node.name;
      if (ts.isInterfaceDeclaration(node)) return node.name;
      if (ts.isTypeAliasDeclaration(node)) return node.name;
      if (ts.isEnumMember(node)) return node.name;
      if (ts.isEnumDeclaration(node)) return node.name;
      if (ts.isNamespaceImport(node)) return node.name;
      if (ts.isNamespaceExportDeclaration(node)) return node.name;
      if (ts.isNamespaceExport(node)) return node.name;
      if (ts.isExportSpecifier(node)) return node.name;
      if (ts.isGetAccessorDeclaration(node)) return node.name;
      if (ts.isSetAccessorDeclaration(node)) return node.name;
      if (ts.isMethodSignatureDeclaration(node)) return node.name;
      if (ts.isMethodDeclaration(node)) return node.name;
      if (ts.isPropertySignatureDeclaration(node)) return node.name;
      if (ts.isPropertyDeclaration(node)) return node.name;
      if (ts.isFunctionExpression(node)) return node.name;
      if (ts.isPropertyAccessExpression(node)) return node.name;
      if (ts.isMetaProperty(node)) return node.name;
      if (ts.isPropertyAssignment(node)) return node.name;
      if (ts.isShorthandPropertyAssignment(node)) return node.name;
      if (ts.isImportAttribute(node)) return node.name;
      if (ts.isNamedTupleMember(node)) return node.name;
      if (ts.isJsxNamespacedName(node)) return node.name;
      if (ts.isJsxAttribute(node)) return node.name;
      if (ts.isJSDocCallbackTag(node)) return node.name;
      if (ts.isJSDocTypedefTag(node)) return node.name;
      if (ts.isJSDocNameReference(node)) return node.name;
      if (ts.isModuleDeclaration(node)) return node.name;
      if (ts.isImportEqualsDeclaration(node)) return node.name;
      if (ts.isImportClause(node)) return node.name;
      if (ts.isImportSpecifier(node)) return node.name;
      if (ts.isJSDocLink(node)) return node.name;
      if (ts.isJSDocLinkPlain(node)) return node.name;
      if (ts.isJSDocLinkCode(node)) return node.name;
      if (ts.isTypeParameterDeclaration(node)) return node.name;
      if (ts.isJSDocParameterTag(node)) return node.name;
      if (ts.isJSDocPropertyTag(node)) return node.name;
      return undefined;
    case "propertyName":
      if (ts.isBindingElement(node)) return node.propertyName;
      if (ts.isExportSpecifier(node)) return node.propertyName;
      if (ts.isImportSpecifier(node)) return node.propertyName;
      return undefined;
    case "label":
      if (ts.isBreakStatement(node)) return node.label;
      if (ts.isContinueStatement(node)) return node.label;
      if (ts.isLabeledStatement(node)) return node.label;
      return undefined;
    case "type":
      if (ts.isVariableDeclaration(node)) return node.type;
      if (ts.isParameterDeclaration(node)) return node.type;
      if (ts.isFunctionDeclaration(node)) return node.type;
      if (ts.isTypeAliasDeclaration(node)) return node.type;
      if (ts.isExportAssignment(node)) return node.type;
      if (ts.isCallSignatureDeclaration(node)) return node.type;
      if (ts.isConstructSignatureDeclaration(node)) return node.type;
      if (ts.isConstructorDeclaration(node)) return node.type;
      if (ts.isGetAccessorDeclaration(node)) return node.type;
      if (ts.isSetAccessorDeclaration(node)) return node.type;
      if (ts.isIndexSignatureDeclaration(node)) return node.type;
      if (ts.isMethodSignatureDeclaration(node)) return node.type;
      if (ts.isMethodDeclaration(node)) return node.type;
      if (ts.isPropertySignatureDeclaration(node)) return node.type;
      if (ts.isPropertyDeclaration(node)) return node.type;
      if (ts.isBinaryExpression(node)) return node.type;
      if (ts.isArrowFunction(node)) return node.type;
      if (ts.isFunctionExpression(node)) return node.type;
      if (ts.isAsExpression(node)) return node.type;
      if (ts.isSatisfiesExpression(node)) return node.type;
      if (ts.isPropertyAssignment(node)) return node.type;
      if (ts.isShorthandPropertyAssignment(node)) return node.type;
      if (ts.isTypeAssertion(node)) return node.type;
      if (ts.isTypeOperatorNode(node)) return node.type;
      if (ts.isTypePredicateNode(node)) return node.type;
      if (ts.isMappedTypeNode(node)) return node.type;
      if (ts.isNamedTupleMember(node)) return node.type;
      if (ts.isOptionalTypeNode(node)) return node.type;
      if (ts.isRestTypeNode(node)) return node.type;
      if (ts.isParenthesizedTypeNode(node)) return node.type;
      if (ts.isFunctionTypeNode(node)) return node.type;
      if (ts.isConstructorTypeNode(node)) return node.type;
      if (ts.isTemplateLiteralTypeSpan(node)) return node.type;
      if (ts.isJSDocTypeExpression(node)) return node.type;
      if (ts.isJSDocNonNullableType(node)) return node.type;
      if (ts.isJSDocNullableType(node)) return node.type;
      if (ts.isJSDocVariadicType(node)) return node.type;
      if (ts.isJSDocOptionalType(node)) return node.type;
      if (ts.isJSDocSignature(node)) return node.type;
      return undefined;
    case "questionToken":
      if (ts.isParameterDeclaration(node)) return node.questionToken;
      if (ts.isConditionalExpression(node)) return node.questionToken;
      if (ts.isMappedTypeNode(node)) return node.questionToken;
      if (ts.isNamedTupleMember(node)) return node.questionToken;
      return undefined;
    case "postfixToken":
      if (ts.isMethodSignatureDeclaration(node)) return node.postfixToken;
      if (ts.isMethodDeclaration(node)) return node.postfixToken;
      if (ts.isPropertySignatureDeclaration(node)) return node.postfixToken;
      if (ts.isPropertyDeclaration(node)) return node.postfixToken;
      if (ts.isPropertyAssignment(node)) return node.postfixToken;
      if (ts.isShorthandPropertyAssignment(node)) return node.postfixToken;
      return undefined;
  }
}

/** A list of children of `node`: empty where its kind carries none or none
 * is written. */
export function childrenOf(node: Node, key: Children): Modifies<{ values: "any"; stores: "grow" }, readonly Node[]> {
  switch (key) {
    case "modifiers":
      if (ts.isVariableStatement(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isParameterDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isMissingDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isFunctionDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isClassDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isClassExpression(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isInterfaceDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isTypeAliasDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isEnumDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isImportDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isExportAssignment(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isNamespaceExportDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isConstructorDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isGetAccessorDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isSetAccessorDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isIndexSignatureDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isMethodSignatureDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isMethodDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isPropertySignatureDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isPropertyDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isClassStaticBlockDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isBinaryExpression(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isArrowFunction(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isFunctionExpression(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isPropertyAssignment(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isShorthandPropertyAssignment(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isConstructorTypeNode(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isModuleDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isImportEqualsDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isExportDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      if (ts.isTypeParameterDeclaration(node)) return node.modifiers?.filter(() => true) ?? [];
      return [];
    case "typeParameters":
      if (ts.isFunctionDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isClassDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isClassExpression(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isInterfaceDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isTypeAliasDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isCallSignatureDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isConstructSignatureDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isConstructorDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isGetAccessorDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isSetAccessorDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isMethodSignatureDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isMethodDeclaration(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isArrowFunction(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isFunctionExpression(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isFunctionTypeNode(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isConstructorTypeNode(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isJSDocTemplateTag(node)) return node.typeParameters?.filter(() => true) ?? [];
      if (ts.isJSDocSignature(node)) return node.typeParameters?.filter(() => true) ?? [];
      return [];
    case "parameters":
      if (ts.isFunctionDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isCallSignatureDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isConstructSignatureDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isConstructorDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isGetAccessorDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isSetAccessorDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isIndexSignatureDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isMethodSignatureDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isMethodDeclaration(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isArrowFunction(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isFunctionExpression(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isFunctionTypeNode(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isConstructorTypeNode(node)) return node.parameters?.filter(() => true) ?? [];
      if (ts.isJSDocSignature(node)) return node.parameters?.filter(() => true) ?? [];
      return [];
  }
}

/** The type arguments written at an application: the declared
 * `typeArguments` of the nine kinds whose child list holds that field
 * (`childProperties` of the package's `dist/api/node/protocol.generated.js`),
 * none for another kind (SOURCE-REWRITES.md, "A node's child read through
 * `Reflect.get`"). */
export function typeArgumentsOf(node: Node): Modifies<{}, readonly TypeNode[]> {
  const written = ts.isTypeReferenceNode(node) || ts.isExpressionWithTypeArguments(node) || ts.isTypeQueryNode(node) ||
      ts.isImportTypeNode(node) || ts.isCallExpression(node) || ts.isNewExpression(node) ||
      ts.isTaggedTemplateExpression(node) || ts.isJsxOpeningElement(node) || ts.isJsxSelfClosingElement(node)
    ? node.typeArguments : undefined;
  return written ?? [];
}

/** The name a declaration or member declares, where its kind has one. */
export const nameOf = (node: Node): Modifies<{}, Node | undefined> => childOf(node, "name");

/** Whether `node` is a type alias declaration of a TypeScript file, by its
 * kind. The compiler's `isTypeAliasDeclaration` also accepts a JavaScript
 * file's JSDoc `@typedef` (`JSTypeAliasDeclaration`, a kind of its own,
 * COMPILER-API.md, "Audited shapes"), so its true edge gives no
 * `TypeAliasDeclaration`; this test's does. It changes nothing, which its
 * promise's type states (SOURCE-ELABORATION.md, "Stated effects"). */
export function isTypeAlias(node: Node): node is Modifies<{}, TypeAliasDeclaration> {
  return node.kind === ts.SyntaxKind.TypeAliasDeclaration;
}

/** Whether `node` is an import declaration of a TypeScript file, by its
 * kind. The compiler's `isImportDeclaration` also accepts a JavaScript
 * file's `JSImportDeclaration` (a kind of its own, COMPILER-API.md, "Audited
 * shapes"), so its true edge gives no `ImportDeclaration`; this test's does.
 * It changes nothing, which its promise's type states. */
export function isImport(node: Node): node is Modifies<{}, ImportDeclaration> {
  return node.kind === ts.SyntaxKind.ImportDeclaration;
}

/** Whether a member is written `static`. */
export const isStatic = (node: Node): Modifies<{ values: "any"; stores: "grow" }, boolean> =>
  childrenOf(node, "modifiers").some((m) => m.kind === ts.SyntaxKind.StaticKeyword);

/** A named property access in either spelling — `e.k`, or `e["k"]` at a
 * string literal or a template without substitutions, no optional chain —
 * as TypeScript gives the spellings one meaning (#119): the object, the
 * key's text, and the key's own node. Null otherwise. */
export function namedAccess(node: Node): { object: Node; key: string; keyNode: Node } | null {
  if (ts.isPropertyAccessExpression(node) && !node.questionDotToken && ts.isIdentifier(node.name))
    return { object: node.expression, key: node.name.text, keyNode: node.name };
  if (ts.isElementAccessExpression(node) && !node.questionDotToken &&
      (ts.isStringLiteral(node.argumentExpression) || ts.isNoSubstitutionTemplateLiteral(node.argumentExpression)))
    return { object: node.expression, key: node.argumentExpression.text, keyNode: node.argumentExpression };
  return null;
}

/** The node with every parenthesized wrapper stripped: TypeScript gives a
 * wrapped and an unwritten expression one meaning, so a decision that reads
 * the normalized form treats the spellings alike (#119). */
export function unparenthesized(node: Node): Node {
  return ts.isParenthesizedExpression(node) ? unparenthesized(node.expression) : node;
}
