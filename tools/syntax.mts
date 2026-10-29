/* A syntax node's optional children, read by checking. The compiler's tree
 * types a class member, a type element or a declaration in general without
 * the `name`, `modifiers` or `type` most of their kinds carry; a tool that
 * handles such a node without first asking which kind it is reads those
 * children here, where each one is checked to be a node.
 */
import * as ts from "typescript/unstable/ast";
import type { Node, TypeAliasDeclaration, TypeNode } from "typescript/unstable/ast";

/** The compiler's syntax module as the front end resolves it, for the suites
 * outside tools/ that read trees (tests/host-families.mts). */
export * as syntax from "typescript/unstable/ast";
/** The compiler's sync API as the front end resolves it, for the suites
 * outside tools/ that call it (tests/compiler-api.mts). */
export * as sync from "typescript/unstable/sync";

/** A child of the compiler's tree: an object with a syntax kind. */
const isNode = (value: unknown): value is Node =>
  typeof value === "object" && value !== null && "kind" in value && typeof value.kind === "number";

/** The children a node's kinds may carry, by the field that holds them. */
type Child = "name" | "propertyName" | "label" | "type" | "questionToken" | "postfixToken";
type Children = "modifiers" | "typeParameters" | "parameters";

/** One child of `node`, where its kind carries it and it is present. */
export function childOf(node: Node, key: Child): Within<{ value: "any"; store: "grow" }, Node | undefined> {
  const value: unknown = Reflect.get(node, key);
  return isNode(value) ? value : undefined;
}

/** A list of children of `node`: empty where its kind carries none or none
 * is written. */
export function childrenOf(node: Node, key: Children): Within<{ value: "any"; store: "grow" }, readonly Node[]> {
  const value: unknown = Reflect.get(node, key);
  return Array.isArray(value) ? value.filter(isNode) : [];
}

/** The type arguments written at an application: the declared
 * `typeArguments` of the nine kinds whose child list holds that field
 * (`childProperties` of the package's `dist/api/node/protocol.generated.js`),
 * none for another kind (SOURCE-REWRITES.md, "A node's child read through
 * `Reflect.get`"). */
export function typeArgumentsOf(node: Node): Within<{ value: "keep"; store: "keep" }, readonly TypeNode[]> {
  const written = ts.isTypeReferenceNode(node) || ts.isExpressionWithTypeArguments(node) || ts.isTypeQueryNode(node) ||
      ts.isImportTypeNode(node) || ts.isCallExpression(node) || ts.isNewExpression(node) ||
      ts.isTaggedTemplateExpression(node) || ts.isJsxOpeningElement(node) || ts.isJsxSelfClosingElement(node)
    ? node.typeArguments : undefined;
  return written ?? [];
}

/** The name a declaration or member declares, where its kind has one. */
export const nameOf = (node: Node): Within<{ value: "any"; store: "grow" }, Node | undefined> => childOf(node, "name");

/** Whether `node` is a type alias declaration of a TypeScript file, by its
 * kind. The compiler's `isTypeAliasDeclaration` also accepts a JavaScript
 * file's JSDoc `@typedef` (`JSTypeAliasDeclaration`, a kind of its own,
 * COMPILER-API.md, "Audited shapes"), so its true edge gives no
 * `TypeAliasDeclaration`; this test's does. It changes nothing, which its
 * promise's type states (SOURCE-ELABORATION.md, "Stated effects"). */
export function isTypeAlias(node: Node): node is Within<{ value: "keep"; store: "keep" }, TypeAliasDeclaration> {
  return node.kind === ts.SyntaxKind.TypeAliasDeclaration;
}

/** Whether a member is written `static`. */
export const isStatic = (node: Node): Within<{ value: "any"; store: "grow" }, boolean> =>
  childrenOf(node, "modifiers").some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
