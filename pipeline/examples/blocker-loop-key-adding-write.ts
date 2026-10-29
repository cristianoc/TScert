// A key-adding write in a loop on a local's own fresh object, which no
// statement of the loop lets escape: at a key known only at run time, as a
// type's metadata is collected key by key; at a named optional key, with a
// return leaving the loop, as an index is recorded once; and in a nested
// loop, the object stable in both.
// Census functions:
// claim-text.mts#atomText, claim-text.mts#bareAtomText,
// claim-text.mts#typeText, claim-text.mts#printType,
// claim-text.mts#liftClause, claim-text.mts#liftSignatures,
// claim-text.mts#liftType, claim-text.mts#liftLabels,
// claim-text.mts#treeAtom, claim-text.mts#lift,
// computed-types.mts#inferredTerm, computed-types.mts#typeQuery.
export function lengths(names: readonly string[]): { [key: string]: number } {
  const metadata: { [key: string]: number } = {};
  for (const key of names) metadata[key] = key.length;
  return metadata;
}

export function firstIndex(
  values: readonly number[],
): { first: number | null; negative?: number } | null {
  const indexes: { first: number | null; negative?: number } = { first: null };
  for (const value of values) {
    if (value > 100) return null;
    if (indexes.first === null) indexes.first = value;
    else if (value < 0) indexes.negative = value;
  }
  return indexes;
}

export function counts(rows: readonly (readonly string[])[]): {
  [key: string]: number;
} {
  const seen: { [key: string]: number } = {};
  let i = 0;
  while (i < rows.length) {
    const row = rows[i];
    if (row !== undefined) for (const key of row) seen[key] = i;
    i = i + 1;
  }
  return seen;
}
