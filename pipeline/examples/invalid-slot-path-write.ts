// A write of a slot root between the path's test and its read: the read
// links were of the object the slot held before, so the read is of the
// written value's declared member, which one arm lacks (TypeScript also
// refuses it, TS2339). Under Node the read gives `undefined` where a string
// is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Index = { readonly kind: "index"; readonly key: Expr };

export function keyText(e: Index, other: Index): string {
  let target = e;
  if (target.key.kind === "name") {
    target = other;
    return target.key.text;
  }
  return "";
}
