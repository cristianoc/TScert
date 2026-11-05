// A test that an optional `never` field is defined drops the arm declaring
// it: the read found the key present, at a type no value has.
// Census functions:
// written-applications.mts#writtenApplications.
type Determined =
  | { nodes: number[]; inferred?: never }
  | { inferred: string | null };
export function count(d: Determined): number {
  if (d.inferred !== undefined) return -1;
  return d.nodes.length;
}
