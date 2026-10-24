// The stand-in family's guards: `isName` an equality, `isExpression` through
// a helper of its tag, `isNameType` a guard of the tag itself, which answers
// `false` on `undefined`; and outside the recognition contract
// `isNameLoosely`, whose answer depends on an option argument,
// `isNameOrAbsent`, which answers `true` on `undefined`, `isNameOptional`,
// which reads the tag through an optional chain and answers `false` there,
// `isSameType`, which compares its argument with itself, `isConstantType`,
// which compares two constants, also in parentheses (`isParenthesizedType`),
// `isNameOfConstant`, which calls a helper on a constant: these answer
// `true` on `undefined` and on strings no tag is; and `isCallAfterConstant`,
// whose local holds a constant, not its tag, so it throws on `undefined`
// only after a step the grammar does not have.
import { UnitType } from "./kinds.js";
export { UnitType };
function isExpressionKind(type) {
    return type === UnitType.Name
        || type === UnitType.Call;
}
export function isName(node) {
    return node.type === UnitType.Name;
}
export function isExpression(node) {
    return isExpressionKind(node.type);
}
export function isNameLoosely(node, loose) {
    return loose ? node.type !== UnitType.Literal : node.type === UnitType.Name;
}
export function isNameType(type) {
    return type === UnitType.Name;
}
export function isNameOrAbsent(node) {
    return node === undefined || node.type === UnitType.Name;
}
export function isNameOptional(node) {
    return node?.type === UnitType.Name;
}
export function isSameType(type) {
    return type === type;
}
export function isConstantType(type) {
    return UnitType.Name === UnitType.Name;
}
export function isNameOfConstant(type) {
    return isNameType(UnitType.Name);
}
export function isParenthesizedType(type) {
    return (UnitType.Name) === UnitType.Name;
}
export function isCallAfterConstant(node) {
    const kind = UnitType.Call;
    return node.type === kind;
}
