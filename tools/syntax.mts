/* A syntax node's optional children, read by checking. The compiler's tree
 * types a class member, a type element or a declaration in general without
 * the `name`, `modifiers` or `type` most of their kinds carry; a tool that
 * handles such a node without first asking which kind it is reads those
 * children here, where each one is checked to be a node.
 */
import * as ts from "typescript/unstable/ast";
import type { Node, TypeAliasDeclaration } from "typescript/unstable/ast";

/** The compiler's syntax module as the front end resolves it, for the suites
 * outside tools/ that read trees (tests/host-families.mts). */
export * as syntax from "typescript/unstable/ast";

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

/** The name a declaration or member declares, where its kind has one. */
export const nameOf = (node: Node): Within<{ value: "any"; store: "grow" }, Node | undefined> => childOf(node, "name");

/** Whether `node` is a type alias declaration of a TypeScript file, by its
 * kind. The compiler's `isTypeAliasDeclaration` also accepts a JavaScript
 * file's JSDoc `@typedef` (`JSTypeAliasDeclaration`, a kind of its own),
 * which the compiler-API contract describes by the members every node has
 * (COMPILER-API.md, "The node invariant"). */
export function isTypeAlias(node: Node): node is TypeAliasDeclaration {
  return node.kind === ts.SyntaxKind.TypeAliasDeclaration;
}

/** Whether a member is written `static`. */
export const isStatic = (node: Node): Within<{ value: "any"; store: "grow" }, boolean> =>
  childrenOf(node, "modifiers").some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
