// A native call's callback in the loop body writes the tested field: after
// the loop the field holds the record without `statements`, whose `length`
// read throws (run under Node).
type Statement = { k: "block"; statements: readonly number[] } | { k: "empty" };
type Holder = { statement: Statement };

export function count(node: Holder, alias: Holder): number {
  if (node.statement.k !== "block") return 0;
  let n = 0;
  for (const s of node.statement.statements) {
    n += s;
    [s].forEach(() => {
      alias.statement = { k: "empty" };
    });
  }
  return n + node.statement.statements.length;
}
