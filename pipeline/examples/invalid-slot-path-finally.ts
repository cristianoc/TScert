// A slot root written in a `try` block and read in its `finally`: the block
// is entered from the write as well as from before it, so the read is of
// the declared member, which one arm lacks (TypeScript also refuses it,
// TS2339). Under Node the read gives `undefined` where a string is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Index = { readonly kind: "index"; readonly key: Expr };

export function keyText(e: Index, other: Index, check: () => void): string {
  let target = e;
  let out = "";
  if (target.key.kind !== "name") return "";
  try {
    target = other;
    check();
  } finally {
    out = target.key.text;
  }
  return out;
}
