/* A syntax node's optional children, read by checking. The compiler's tree
 * types a class member, a type element or a declaration in general without
 * the `name`, `modifiers` or `type` most of their kinds carry; a tool that
 * handles such a node without first asking which kind it is reads those
 * children here, where each one is checked to be a node.
 */
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";

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
export function childOf(node: Node, key: Child): Node | undefined {
  const value: unknown = Reflect.get(node, key);
  return isNode(value) ? value : undefined;
}

/** A list of children of `node`: empty where its kind carries none or none
 * is written. */
export function childrenOf(node: Node, key: Children): readonly Node[] {
  const value: unknown = Reflect.get(node, key);
  return Array.isArray(value) ? value.filter(isNode) : [];
}

/** The name a declaration or member declares, where its kind has one. */
export const nameOf = (node: Node): Node | undefined => childOf(node, "name");

/** Whether a member is written `static`. */
export const isStatic = (node: Node): boolean =>
  childrenOf(node, "modifiers").some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
