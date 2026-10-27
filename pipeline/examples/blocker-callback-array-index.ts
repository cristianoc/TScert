// The index forEach passes its callback, read in another array through an
// optional chain: `%ElementAt%` on the chain's present value, the element or
// `undefined`.
// Census functions:
// computed-types.mts#parameterMembers, declaration-graph.mts#mergedParameters.
import type {
  TypeReferenceNode,
  TypeParameterDeclaration,
} from "typescript/unstable/ast";
export function use(
  node: TypeReferenceNode,
  parameters: readonly TypeParameterDeclaration[],
): void {
  parameters.forEach((parameter, index) => {
    const written = node.typeArguments?.[index];
  });
}
