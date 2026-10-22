// A node list or a fresh empty array, `alias.typeParameters ?? []`, its
// `length` compared in a branch test, as `readTypeTerm`'s associated-result
// alias check has it: each member of the union is one array contract, whose
// `length` is its store's (PROGRAM-TYPING.md, the `len` rule of a union of
// arrays).
import * as ts from "typescript/unstable/ast";

export function differs(
  alias: ts.TypeAliasDeclaration,
  arguments_: readonly number[],
): boolean {
  const parameters = alias.typeParameters ?? [];
  if (arguments_.length !== parameters.length) return true;
  return false;
}

export function differsOrNamed(
  alias: ts.TypeAliasDeclaration,
  arguments_: readonly number[],
): boolean {
  const parameters = alias.typeParameters ?? [];
  return (
    arguments_.length !== parameters.length ||
    parameters.some((p) => p.constraint !== undefined)
  );
}
