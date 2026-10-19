// The stand-in family's guards: `isName` an equality, `isExpression` through
// a helper of its tag, and `isNameLoosely`, whose answer depends on an option
// argument, outside the recognition contract.
import { SyntaxKind } from "./kinds.js";
export { SyntaxKind };
function isExpressionKind(type) {
    return type === SyntaxKind.Name
        || type === SyntaxKind.Call;
}
export function isName(node) {
    return node.type === SyntaxKind.Name;
}
export function isExpression(node) {
    return isExpressionKind(node.type);
}
export function isNameLoosely(node, loose) {
    return loose ? node.type !== SyntaxKind.Literal : node.type === SyntaxKind.Name;
}
