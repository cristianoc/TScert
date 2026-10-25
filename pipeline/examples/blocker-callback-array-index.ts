// A callback index and an iterator index need their array-index fact available
// at an indexed read.
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
