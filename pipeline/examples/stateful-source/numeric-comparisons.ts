// Both reads are stable snapshots. Comparing against a named zero eliminates
// that numeric singleton from the other snapshot's union.
function namedZero(seed: 0 | 1, zeroSeed: 0): 1 {
  const box = { value: seed, zero: zeroSeed };
  const value = box.value;
  const zero = box.zero;
  if (value !== zero) return value;
  return 1;
}

// The same comparison works in a delayed closure body.
function numericClosure(value: 0 | 1): () => boolean {
  return (): boolean => value === 1;
}

// The left read happens before the call overwrites the field on the right.
function comparisonEffects(seed: 0 | 1, zero: 0): boolean {
  const cell: { value: 0 | 1 } = { value: seed };
  const clear = (): 0 => {
    cell.value = zero;
    return zero;
  };
  return cell.value !== clear();
}
