// for-of over an indexed array with an empty-array fallback.
// Census functions:
// fragment-statements.mts#patternStmt
// fragment-statements.mts#protocolPattern
// fragment-statements.mts#hoistTarget
// fragment-statements.mts#readScope
// fragment-statements.mts#readCannotThrow
// fragment-statements.mts#unassigned
// fragment-statements.mts#block
// fragment-statements.mts#statements
// fragment-statements.mts#functionPlacement
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
export function place(mentions: readonly Set<string>[], i: number): void {
  for (const f of mentions[i] ?? []) {
    const name = f;
  }
}
