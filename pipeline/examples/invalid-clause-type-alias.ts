// Negative case: after unwrapping a non-record array type alias in a clause,
// an off-by-one precondition (`i <= xs.length`) permits reading `xs[xs.length]`
// (`undefined`), yielding `NaN` at runtime.

type NumList = Dense<number[]>;
type Pair = { xs: NumList; ys: NumList };
type PairAlias = Pair;

/** @requires 0 <= i && i <= p.xs.length && p.xs.length === p.ys.length */
function readPastAliasEnd(p: PairAlias, i: SafeInt): number {
  return p.xs[i]! + p.ys[i]!;
}
