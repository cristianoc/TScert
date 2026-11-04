// A property assignment needs to build its fresh array at the field storage
// contract.
// Census functions:
// fragment-statements.mts#abrupt, fragment-statements.mts#block,
// fragment-statements.mts#controlStmt, fragment-statements.mts#declarations,
// fragment-statements.mts#forInStmt, fragment-statements.mts#forStmt,
// fragment-statements.mts#hoistTarget, fragment-statements.mts#hoisting,
// fragment-statements.mts#letPattern, fragment-statements.mts#markEarly,
// fragment-statements.mts#neverAssigned, fragment-statements.mts#patternStmt,
// fragment-statements.mts#protocolForOf,
// fragment-statements.mts#protocolPattern,
// fragment-statements.mts#readScope,
// fragment-statements.mts#statements, fragment-statements.mts#stmt,
// fragment-statements.mts#switchStmt, fragment-statements.mts#tryStmt,
// fragment-statements.mts#unassigned.
export function reset(g: { items: number[] }): void {
  g.items = [];
}
