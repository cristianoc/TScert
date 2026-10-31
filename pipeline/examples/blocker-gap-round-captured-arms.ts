// Captured array read before flatMap calls each element's function.
// Census functions:
// claim-text.mts#liftClause
// claim-text.mts#liftSignatures
// claim-text.mts#liftType
// claim-text.mts#liftLabels
// claim-text.mts#treeAtom
// claim-text.mts#lift
type Arm = { count: number; lift: (limit?: number) => string[] };
export function lift(
  labels: readonly string[],
  limit: number,
  split: (s: string) => string[],
): string[] {
  const arms = labels.map((label): Arm => {
    const clauses = split(label);
    return {
      count: clauses.length,
      lift: (limit) => clauses.slice(0, limit).map((clause) => clause),
    };
  });
  const total = arms.reduce((n, arm) => n + arm.count, 0);
  if (total > limit) {
    const atoms: string[] = [];
    for (const arm of arms) {
      if (atoms.length >= limit) break;
      atoms.push(...arm.lift(limit - atoms.length));
    }
    return atoms;
  }
  return arms.flatMap((arm) => arm.lift());
}
