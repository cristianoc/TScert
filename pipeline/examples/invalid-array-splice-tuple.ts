// `splice` may shorten its receiver's store, which a tuple's contract fixes at
// two positions: TypeScript admits the call and types `pair[1]` a number,
// and under Node `emptied([1, 2])` is `undefined`. `splice` is stated at a
// mutable array, which a tuple is not, so the call is refused.
export function emptied(pair: [number, number]): number {
  pair.splice(0);
  return pair[1];
}
