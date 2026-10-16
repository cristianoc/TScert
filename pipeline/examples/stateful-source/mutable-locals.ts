/**
 * Mutable locals. A `let` allocates a private cell the source never sees as a
 * value: reading the name reads the cell, assigning writes it, and a closure
 * holds the cell's identity, so it observes later writes. The annotation is
 * the storage contract every assignment is checked against.
 */

/** A captured reader observes a write made after it was created. */
function capturedReaderObservesWrite(seed: boolean): boolean {
  let value: boolean = seed;
  const read = (): boolean => value;
  value = false;
  return read();
}

/** An immutable snapshot holds the value, not the location, and survives. */
function snapshotSurvivesWrite(seed: boolean): boolean {
  let value: boolean = seed;
  const saved: boolean = value;
  const read = (): boolean => saved;
  value = false;
  return read();
}

/** Assignment is an expression: it yields the value written, not the write. */
function assignmentYieldsValue(seed: boolean): boolean {
  let state: boolean = seed;
  const result: boolean = (state = false);
  return result;
}

/** A captured writer, then a read through the cell. */
function capturedWriterThenRead(seed: boolean): boolean {
  let value: boolean = seed;
  const reset = (): boolean => (value = false);
  const ignored: boolean = reset();
  return value;
}

/** The null test concerns the value, never the hidden location's object tag. */
function mutableTag(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  return value === null ? false : true;
}

/** Replacing the location with the saved left operand would prevent this write. */
function mutableFallback(seed: boolean | null): boolean {
  let value: boolean | null = seed;
  return value ?? (value = true);
}

/** A Boolean guard must leave the mutable location intact in either arm. */
function mutableBranch(seed: boolean): boolean {
  let value: boolean = seed;
  if (value) {
    value = false;
  } else {
    value = true;
  }
  return value;
}

/**
 * The original true value is saved before the mutable cell is overwritten.
 * TypeScript exports the initial singleton and the verifier checks it.
 */
function preciseSnapshot(seed: true): true {
  let value: boolean = seed;
  const saved: true = value;
  const read = (): true => saved;
  value = false;
  return read();
}

/** Sibling scopes can reuse a name without sharing an inferred contract. */
function inferredSiblingContracts(seed: boolean): number | boolean {
  if (seed) {
    let value = 1;
    return value;
  } else {
    let value = false;
    return value;
  }
}
