// A read through an optional key that gives something other than
// `undefined` finds the key present, and its value at the key: an arm whose
// optional key's type the test contradicts is dropped, an empty type
// contradicting every test (`never`).
type Determined = { nodes: number[]; inferred?: never } | { inferred: string | null };
export function count(d: Determined): number {
  if (d.inferred !== undefined) return d.inferred === null ? 0 : d.inferred.length;
  return d.nodes.length;
}

// An optional key's type the test does not contradict keeps its arm.
type Kept = { nodes: number[]; inferred?: string | null } | { inferred: string | null; other: number };
export function kept(d: Kept): number {
  if (d.inferred !== undefined) return d.inferred === null ? 0 : 2;
  return 1;
}

// A test `undefined` passes says nothing of an optional key's presence:
// the object may lack it.
type Absent = { nodes: number[]; tag?: string } | { tag: null; spare: number };
export function absent(u: Absent): number {
  if (u.tag === undefined) return 0;
  return 1;
}
