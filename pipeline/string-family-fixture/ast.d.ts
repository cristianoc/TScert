// A stand-in host package of a string-tagged family, which no audited
// package has: pipeline/test.mts installs it as the host through the
// test-only stand-ins, with a description and a guard table of its own
// (HOST-FAMILIES.md, "Instances"). Its units are tagged by `type`.
import { SyntaxKind } from "./kinds.js";
export { SyntaxKind };
export interface Unit {
  readonly type: SyntaxKind;
  readonly start: number;
  /** A fresh array on each read: the stand-in's allocating member. */
  readonly notes: readonly string[];
}
export interface Name extends Unit {
  readonly type: SyntaxKind.Name;
  readonly name: string;
}
export interface Call extends Unit {
  readonly type: SyntaxKind.Call;
  readonly callee: Unit;
}
export interface Literal extends Unit {
  readonly type: SyntaxKind.Literal;
  readonly value: string;
}
export declare function isName(node: Unit): node is Name;
export declare function isExpression(node: Unit): node is Name | Call;
export declare function isNameLoosely(node: Unit, loose?: boolean): node is Name;
