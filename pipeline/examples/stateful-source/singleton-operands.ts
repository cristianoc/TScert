/**
 * A strict comparison refines the tested read when the other operand's
 * claimed type is a singleton. The operand need not be a literal: a name or a
 * field read is effect-free, so saving the tested read before it changes
 * nothing. A call could change the tested cell, so it is not accepted there.
 */
/** The other operand is a field of a local object built from a singleton. */
function inferredFieldComparison(x: { value: 0 | 1 }, zeroSeed: 0): 1 {
  const other = { zero: zeroSeed };
  if (x.value !== other.zero) return x.value;
  return 1;
}
/** The other operand is a parameter. */
function comparedToParameter(x: { value: 0 | 1 }, zero: 0): 1 {
  if (x.value !== zero) return x.value;
  return 1;
}
/** The tested read is on the right. */
function reversedOperands(x: { value: 0 | 1 }, zero: 0): 1 {
  if (zero !== x.value) return x.value;
  return 1;
}
/** Equality selects the other arm. */
function equalBranch(x: { value: 0 | 1 }, zero: 0): 0 {
  if (x.value === zero) return x.value;
  return 0;
}
/** A mutable local's cell is refined the same way. */
function localCellCompared(flag: 0 | 1, zero: 0): 1 {
  let current = flag;
  if (current !== zero) return current;
  return 1;
}
