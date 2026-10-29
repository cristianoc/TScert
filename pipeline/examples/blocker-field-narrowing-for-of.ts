// A test of a field narrows a later read of that field only across steps
// keeping the heap. A `for...of` loop over an array steps its iterator,
// whose step writes the iterator's position: a call whose footprint is not
// the empty one, so the reread after the loop is at the field's declared
// type, where `statements` is no member of every arm.
// Census functions: fragment-support.mts#forInEntryReads (its
// `declarations[0]` refusal is a consequence: the element `s` has no type).
type Statement = { k: "block"; statements: readonly number[] } | { k: "empty" };

export function count(node: { readonly statement: Statement }): number {
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) n += s;
  return n + node.statement.statements.length;
}
