// A slot root written on a loop's back edge: the test before the loop holds
// on the first iteration alone, so the read in the body is of the declared
// member, which one arm lacks (TypeScript also refuses it, TS2339). Under
// Node the second iteration reads `undefined` where a string is returned.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string };
type Index = { readonly kind: "index"; readonly key: Expr };

export function lastKey(e: Index, next: Index, n: number): string {
  let target = e;
  let out = "";
  if (target.key.kind !== "name") return "";
  for (let i = 0; i < n; i++) {
    out = target.key.text;
    target = next;
  }
  return out;
}
