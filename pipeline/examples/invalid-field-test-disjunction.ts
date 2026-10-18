// Where `n.kind === 1 || b.kind === 2` holds, `n` may be of any arm: the
// disjunction may hold by its right operand alone.
type Shape =
  | { kind: 1; x: number }
  | { kind: 2; x: string }
  | { kind: 3; y: number };

export function either(n: Shape, b: Shape): number | string {
  if (n.kind === 1 || b.kind === 2) {
    // @ts-expect-error: `n` may be the arm without `x`
    return n.x;
  }
  return 0;
}
