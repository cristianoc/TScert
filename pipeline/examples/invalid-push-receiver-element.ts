// A choice one of whose values is outside the receiver's element type: the
// array of `Stmt` would hold a `{ k: "other" }`.
type Stmt = { k: "break"; label: string } | { k: "expr"; value: number };

export function wrong(out: Stmt[], fallback: Stmt | null): string {
  // @ts-expect-error: `{ k: "other" }` is no `Stmt`.
  out.push(fallback ?? { k: "other" });
  const last = out[out.length - 1];
  return last === undefined ? "" : last.k;
}
