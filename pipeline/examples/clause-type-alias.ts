// Positive case: non-record type aliases in @requires / @ensures clauses
// unwrap to their underlying array, view, string, or SafeInt types.

type NumList = Dense<number[]>;
type NestedNumList = NumList;
type Bytes = Uint8Array;
type Idx = SafeInt;

type Pair = {
  xs: NestedNumList;
  ys: NumList;
  flags: Bytes;
};
type PairAlias = Pair;

/** @requires 0 <= i && i < p.xs.length && p.xs.length === p.ys.length && p.xs.length === p.flags.length */
function readThroughAlias(p: PairAlias, i: Idx): number {
  return p.xs[i]! + p.ys[i]! + p.flags[i]!;
}

/** @requires xs.length === ys.length && 0 <= i && i < xs.length */
function sumThroughAlias(xs: NestedNumList, ys: NumList, i: Idx): number {
  return xs[i]! + ys[i]!;
}

/** @ensures result.xs.length === 2 && result.xs.length === result.ys.length && result.xs.length === result.flags.length */
function makePairAlias(a: number, b: number): PairAlias {
  return { xs: [a, b], ys: [b, a], flags: new Uint8Array(2) };
}

function entry(): number {
  const p = makePairAlias(3, 4);
  const p2 = makePairAlias(5, 6);
  return readThroughAlias(p, 1) + sumThroughAlias(p2.xs, p2.ys, 0);
}
