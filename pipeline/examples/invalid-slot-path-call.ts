// A call between a slot root's path test and its read, through a member
// that is not stable (a program record's): the slot survives the call, the
// object's member does not, since the callee may replace it. TypeScript keeps
// the narrowing. Under Node the read gives `undefined` where a string is
// returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Box = { key: Expr };

export function keyText(b: Box, n: number, replace: () => void): string {
  let target = b;
  if (n > 0) target = b;
  if (target.key.kind === "name") {
    replace();
    return target.key.text;
  }
  return "";
}
