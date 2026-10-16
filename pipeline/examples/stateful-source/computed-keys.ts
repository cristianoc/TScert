/**
 * Element access: the receiver is evaluated, then the key, then the field the
 * key's claimed type names is read or written. The key need not be a literal;
 * it must be claimed as one string singleton, and its own claim is checked.
 */
/** A literal key is the field it names. */
function literalKey(x: { value: number | null }): number {
  const value = x["value"];
  return value ?? 0;
}
/** The key's effect happens before the right side reads the local. */
function keyInitializesRhs(): number {
  let x: number | null = null;
  const box = { slot: 0 };
  const before: number = box.slot;
  box[(x = 1) === 1 ? "slot" : "slot"] = x;
  return box.slot;
}
/** A computed key read, with the key's effect before the read. */
function computedRead(box: { slot: number }): number {
  let count: number | null = null;
  return box[(count = 1) === 1 ? "slot" : "slot"];
}
/** Two fields: the key's claim selects which is read. */
function twoFields(box: { a: number; b: 1 }): number {
  return box["a"];
}
