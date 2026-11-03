// Past `k.kind === "c" || !(k.kind === "b")`, `k` is the `"b"` arm: its
// cast to the `"a"` arm is refused (`wrong({ kind: "b", b: 1 })` throws
// under Node).
type K = { kind: "a"; a: string } | { kind: "b"; b: number } | { kind: "c" };
export function wrong(k: K): number {
  if (k.kind === "c" || !(k.kind === "b")) return 0;
  return (k as { kind: "a"; a: string }).a.length;
}
