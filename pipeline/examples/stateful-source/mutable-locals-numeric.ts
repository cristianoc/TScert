/** Numeric storage contracts and checked current-content predicates. */

/**
 * The storage contract is `number`, so the later write meets it and the
 * captured reader observes it. The literal `2` is claimed at the family rather
 * than at its own singleton, which a singleton rule alone cannot type.
 */
function numericCapturedWrite(): number {
  let value: number = 1;
  const read = (): number => value;
  value = 2;
  return read();
}

/**
 * An assignment inside a coalesce: the left arm may short-circuit, so the
 * write happens at most once and the expression still yields what was written
 * rather than the null a bare write would give.
 */
function numericAssignmentInCoalesce(seed: number | undefined): number {
  let state: number | null = null;
  const result: number = seed ?? (state = 1);
  return result;
}

/**
 * The same binding with no annotation. The producer states its contract — the
 * type it gives the name where it first stands in scope, `number` rather than
 * the `1` the initializer produced — and that is what every assignment is
 * checked against. It is supplied and checked, never inferred here.
 */
function inferredStorageContract(): number {
  let value = 1;
  const read = (): number => value;
  value = 2;
  return read();
}

/** A numeric point fact survives closure creation, but not a later write. */
function numericGuardedCapture(): number {
  let value: number | null = null;
  value = 1;
  const read = (): number => {
    if (value !== null) return value;
    return 0;
  };
  value = null;
  return read();
}

/** The written value is arbitrary, so a finite list of constants is insufficient. */
function numericAssignmentSnapshot(seed: number): number {
  let value: number | null = null;
  value = seed;
  const snapshot = value;
  value = null;
  return snapshot;
}

/**
 * A named field guard establishes a snapshot that survives an aliased call.
 * Both producers supply the field-content assertion checked at the read.
 */
function numericAliasSnapshot(seed: number | null): number {
  const cell: { total: number | null } = { total: seed };
  const alias = cell;
  if (cell.total === null) return 0;
  const snapshot: number = cell.total;
  const clear = (): null => {
    alias.total = null;
    return null;
  };
  const ignored = clear();
  return snapshot;
}
