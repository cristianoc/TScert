// A destructuring assignment writes a slot root, then a later target's
// default reads the path in the same statement: the default reads the
// written value, whose member the test before the statement did not see
// (TypeScript also refuses it, TS2339). Under Node the default gives
// `undefined` where a string is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Index = { readonly kind: "index"; readonly key: Expr };

export function keyText(first: Index, other: Index): string {
  let target = first;
  let out = "";
  if (target.key.kind === "name") {
    [target, out = target.key.text] = [other, undefined];
  }
  return out;
}
