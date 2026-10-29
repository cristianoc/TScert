// A loop body writing the field a test narrowed, through another
// reference: after the loop the field holds the record without
// `statements`, whose `length` read throws (run under Node).
type Statement = { k: "block"; statements: readonly number[] } | { k: "empty" };
type Holder = { statement: Statement };

export function count(node: Holder, alias: Holder): number {
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) {
    n += s;
    alias.statement = { k: "empty" };
  }
  return n + node.statement.statements.length;
}
