// A function a record field holds, passed to map: map passes it the index
// and the array after the element, so the field's type states that the
// function takes further actuals, at its rest, and the effect it keeps.
// The record is built from module functions, a parameter and a literal of
// closures, whose code discards the actuals past its parameters.
// Census functions:
// fragment-parse.mts#renamedModule, fragment-parts.mts#astHolds,
// fragment-parts.mts#codeParts, fragment-parts.mts#deepPartMap,
// fragment-parts.mts#directParts, fragment-parts.mts#documentHolds,
// fragment-parts.mts#documentParts, fragment-parts.mts#forEachPart,
// fragment-parts.mts#fragmentTypes, fragment-parts.mts#mapDocument,
// fragment-parts.mts#mapExprParts, fragment-parts.mts#mapFunctionParts,
// fragment-parts.mts#mapStmtParts, fragment-parts.mts#moduleHolds.
type Tree = { k: "leaf"; n: number } | { k: "node"; kids: Tree[] };
type Mapper = {
  tree: (
    t: Tree,
    ...further: unknown[]
  ) => Modifies<{ values: "any"; stores: "grow" }, Tree>;
  num: (
    n: number,
    ...further: unknown[]
  ) => Modifies<{ values: "any"; stores: "grow" }, number>;
};
export function mapParts(
  t: Tree,
  m: Mapper,
): Modifies<{ values: "any"; stores: "grow" }, Tree> {
  switch (t.k) {
    case "leaf":
      return { ...t, n: m.num(t.n) };
    case "node":
      return { ...t, kids: t.kids.map(m.tree) };
  }
}
export function deep(
  num: (
    n: number,
    ...further: unknown[]
  ) => Modifies<{ values: "any"; stores: "grow" }, number>,
): Modifies<{ values: "any"; stores: "grow" }, Mapper> {
  function tree(t: Tree): Tree {
    return mapParts(t, d);
  }
  const d: Mapper = { tree, num };
  return d;
}
export function numbers(
  t: Tree,
): Modifies<{ values: "any"; stores: "grow" }, number[]> {
  const seen: number[] = [];
  mapParts(t, {
    tree: (u) => u,
    num: (n) => {
      seen.push(n);
      return n;
    },
  });
  return seen;
}
export function shifted(ts: Tree[], k: number): Tree[] {
  const num = (n: number): number => n + k;
  return ts.map(deep(num).tree);
}
