// A test of a field narrows its reread after a `for...of` loop over an
// array: the iterator `%Iterate%` returns is a fresh object, separated from
// the fields of the records in scope, readonly views and writable fields
// alike, and each of its steps changes no old location but the iterator's
// own, so the read link of the tested field survives every step.
// Census functions: fragment-support.mts#forInEntryReads (its
// `declarations[0]` refusal is a consequence: the element `s` has no type).
type Statement = { k: "block"; statements: readonly number[] } | { k: "empty" };

export function count(node: { readonly statement: Statement }): number {
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) n += s;
  return n + node.statement.statements.length;
}

export function countWritable(node: { statement: Statement }): number {
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) n += s;
  return n + node.statement.statements.length;
}
