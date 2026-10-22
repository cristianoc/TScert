// `push` onto an array of a union: the receiver fixes the element type, so
// an actual of one arm, or a choice between arms, is pushed at the union.
type Stmt = { k: "break"; label: string } | { k: "expr"; value: number };

export function dispatch(fallback: Stmt | null, label: string): number {
  const out: Stmt[] = [];
  const brk: { k: "break"; label: string } = { k: "break", label };
  out.push(brk);
  out.push(fallback ?? { k: "break", label });
  return out.length;
}
