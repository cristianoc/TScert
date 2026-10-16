/**
 * Numbers in the source fragment. They are opaque: bound, passed, stored in a
 * union and shape-tested, never computed with. The fragment has no arithmetic
 * and no numeric comparison, so nothing here adds up two of them.
 */
function idNumber(x: number): number {
  return x;
}

/** A literal is its own singleton, and the singleton is below the family. */
function literalResult(): number {
  return 2;
}

/** An annotated copy keeps the annotation, exactly as a boolean copy does. */
function copyNumber(x: number): number {
  const y: number = x;
  return y;
}

/** A singleton type is preserved end to end, not widened to the family. */
function singletonNumber(x: 1): 1 {
  return x;
}

/** Nullable numbers refine like any other union member. */
function guardNumber(x: number | null): number {
  if (x !== null) {
    return x;
  }
  return 0;
}

/** Distinct spellings of one double are one literal: `1.0` is `1`. */
function spelledNumber(): 1 {
  return 1.0;
}
