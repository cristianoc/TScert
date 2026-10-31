// Call finding the first optional constructor parameter inside map.
// Census functions:
// fragment-classes.mts#classStmt
// fragment-classes.mts#classBody
import type { ParameterDeclaration } from "typescript/unstable/ast";
function firstOptional(
  params: readonly {
    readonly questionToken?: unknown;
    readonly initializer?: unknown;
  }[],
): Within<{ value: "any"; store: "grow" }, number> {
  return params.findIndex((p) => !!p.questionToken || !!p.initializer);
}
export function lower(params: readonly ParameterDeclaration[]): boolean[] {
  return params.map(
    (p, i, all) => !p.questionToken && !p.initializer && i > firstOptional(all),
  );
}
