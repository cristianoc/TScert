// A `let` a closure writes is a cell, not a slot: the call between the
// path's test and its read replaces the object the root holds, which
// TypeScript does not see. Under Node the read gives `undefined` where a
// string is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Index = { readonly kind: "index"; readonly key: Expr };

export function keyText(e: Index, other: Index): string {
  let target = e;
  const replace = (): void => {
    target = other;
  };
  if (target.key.kind === "name") {
    replace();
    return target.key.text;
  }
  return "";
}
