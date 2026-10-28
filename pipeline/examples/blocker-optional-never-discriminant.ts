// A test that an optional `never` field is undefined needs to narrow the
// union to the arm declaring it.
// Census functions:
// written-applications.mts#writtenApplications.
type Determined =
  | { nodes: number[]; inferred?: never }
  | { inferred: string | null };
export function count(d: Determined): number {
  if (d.inferred !== undefined) return -1;
  return d.nodes.length;
}
