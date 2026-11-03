// Past `!(m.kind === "method") || m.n || m.q`, `m.q` is falsy: its cast to
// a string is refused (`wrong({ kind: "method" })` throws under Node).
type M = { kind: "method"; n?: number; q?: string } | { kind: "field" };
export function wrong(m: M): number {
  if (!(m.kind === "method") || m.n || m.q) return 0;
  return (m.q as string).length;
}
