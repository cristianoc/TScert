// A slot root's object whose member is replaced through an alias between
// the path's test and its read: the slot still holds the object, but the
// write ends the read link through `key`, a program record's member, which
// no stable link keeps. TypeScript keeps the narrowing. Under Node the read
// gives `undefined` where a string is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Box = { key: Expr };

export function keyText(b: Box, other: Expr, n: number): string {
  let target = b;
  if (n > 0) target = b;
  const alias = target;
  if (target.key.kind === "name") {
    alias.key = other;
    return target.key.text;
  }
  return "";
}
