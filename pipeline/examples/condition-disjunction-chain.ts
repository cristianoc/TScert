// A conjunction of disjunctions: the plan holds each later operand under
// both exits of the disjunction before it, so the graph has a path per
// choice of a deciding operand in each disjunction (2^4 here).
export function chain(
  a: string | undefined,
  b: number,
  c: string | undefined,
  d: number,
  e: string | undefined,
  f: number,
  g: string | undefined,
  h: number,
): number {
  if (
    (a !== undefined || b > 0) &&
    (c !== undefined || d > 0) &&
    (e !== undefined || f > 0) &&
    (g !== undefined || h > 0)
  )
    return 1;
  return 0;
}
