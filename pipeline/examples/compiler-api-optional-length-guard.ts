// An optional chain's length as an operand of a condition, followed by a
// guard: `p?.length && g(n)` reads as `p != null && (p.length && g(n))`, and
// after the test of `p` the rest is read for its truthiness alone, so the
// guard's refinement reaches the branch, as `type-term.mts#members` tests a
// generic method signature.
import * as ts from "typescript/unstable/ast";

export function generic(member: ts.TypeElement, methods: boolean): number {
  const typeParameters = ts.isMethodSignatureDeclaration(member)
    ? member.typeParameters
    : undefined;
  if (ts.isPropertySignatureDeclaration(member)) {
    return 1;
  } else if (
    ts.isMethodSignatureDeclaration(member) &&
    methods === true &&
    typeParameters?.length &&
    !member.postfixToken &&
    !member.modifiers?.length
  ) {
    return typeParameters.length;
  }
  return 0;
}

export function guarded(
  member: ts.TypeElement,
  o: readonly number[] | undefined,
): number {
  if (o?.length && ts.isMethodSignatureDeclaration(member))
    return member.parameters.length;
  return 0;
}
