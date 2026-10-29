// A closure created before the loop writes the tested field, and the loop
// body calls it: after the loop the field holds the record without
// `statements`, whose `length` read throws (run under Node).
type Statement = { k: "block"; statements: readonly number[] } | { k: "empty" };
type Holder = { statement: Statement };

export function count(node: Holder, alias: Holder): number {
  const clear = (): void => {
    alias.statement = { k: "empty" };
  };
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) {
    n += s;
    clear();
  }
  return n + node.statement.statements.length;
}
