// Census functions:
// fragment-statements.mts#patternStmt
// fragment-statements.mts#protocolPattern
// fragment-statements.mts#hoistTarget
// fragment-statements.mts#readScope
// fragment-statements.mts#readCannotThrow
// fragment-statements.mts#unassigned
// fragment-statements.mts#block
// fragment-statements.mts#statements
// fragment-statements.mts#markEarly
// fragment-statements.mts#hoisting
// fragment-statements.mts#letPattern
// fragment-statements.mts#forStmt
// fragment-statements.mts#perIterationFor
// fragment-statements.mts#forInStmt
// fragment-statements.mts#protocolForOf
// fragment-statements.mts#switchStmt
// fragment-statements.mts#tryStmt
// fragment-statements.mts#abrupt
// fragment-statements.mts#stmt
// fragment-statements.mts#declarations
// fragment-statements.mts#declarator
// fragment-statements.mts#mutableList
// fragment-statements.mts#declarationsOf
// fragment-statements.mts#neverAssigned
// fragment-statements.mts#controlStmt
type Stmt = { k: "block"; body: Stmt[] } | { k: "end" };
export function blocks(
  clauses: number[],
  statements: (n: number) => Stmt[],
): Stmt[] {
  return clauses.reduce<Stmt[]>(
    (inner, c) => [{ k: "block", body: inner }, ...statements(c)],
    [],
  );
}
