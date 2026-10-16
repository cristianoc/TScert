/**
 * A location under two invariant contracts at once. Conjunction is commutative
 * and idempotent, so the operands are sorted and deduplicated before the
 * reference clause is interned: two spellings of one contract lower to the
 * plain cell the producer claims.
 */
function sameContractTwice(seed: boolean): boolean {
  const cell: { value: boolean } & { value: boolean } = { value: seed };
  return cell.value;
}

/** The operands may be spelled differently and still coincide. */
function spelledTwoWays(seed: boolean): boolean {
  const cell: { value: boolean } & { value: true | false } = { value: seed };
  cell.value = false;
  return cell.value;
}

/** Conjunction is associative and has no arity: three operands, grouped or not. */
function underThree(seed: boolean): boolean {
  const cell: ({ value: boolean } & { value: true | false }) & {
    value: boolean;
  } = {
    value: seed,
  };
  return cell.value;
}
