// The stand-in family's guards: `isName` an equality, `isExpression` through
// a helper of its tag, and `isNameLoosely`, whose answer depends on an option
// argument, outside the recognition contract.
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
