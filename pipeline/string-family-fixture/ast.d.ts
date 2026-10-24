// A stand-in host package of a string-tagged family, which no audited
// package has: pipeline/test.mts activates it through a description of its
// own, with a guard table of its own (HOST-FAMILIES.md, "Instances"). Its
// units are tagged by `type`.
import { UnitType } from "./kinds.js";
export { UnitType };
export interface Unit {
  readonly type: UnitType;
  readonly start: number;
  /** A fresh array on each read: the stand-in's allocating member. */
  readonly notes: readonly string[];
}
export interface Name extends Unit {
  readonly type: UnitType.Name;
  readonly name: string;
}
export interface Call extends Unit {
  readonly type: UnitType.Call;
  readonly callee: Unit;
}
export interface Literal extends Unit {
  readonly type: UnitType.Literal;
  readonly value: string;
}
// Declarations named as the compiler API's named views are, with members
// those views do not list: read by their own declarations.
export interface Program {
  readonly files: readonly string[];
  readonly extra: number;
}
export declare class API {
  readonly name: string;
}
export declare function isName(node: Unit): node is Name;
export declare function isExpression(node: Unit): node is Name | Call;
export declare function isNameLoosely(
  node: Unit,
  loose?: boolean,
): node is Name;
export declare function isNameType(type: UnitType): type is UnitType.Name;
export declare function isNameOrAbsent(node: Unit | undefined): node is Name;
export declare function isNameOptional(node: Unit): node is Name;
export declare function isSameType(type: UnitType): type is UnitType.Name;
export declare function isConstantType(type: UnitType): type is UnitType.Name;
export declare function isNameOfConstant(type: UnitType): type is UnitType.Name;
