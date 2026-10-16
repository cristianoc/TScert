/**
 * A private cell this lowering allocates sits at a location no other object
 * in scope has, so a write to it leaves what is known about a parameter's
 * field in place. Two parameters may be one object, so a write through one
 * forgets what was known about the other.
 */
/** The assigned parameter's own cell is fresh: the guard's fact survives its write. */
function keptAcrossOwnCell(x: { value: number | null }, y: number): number {
  if (x.value === null) return 0;
  const value = (y = x.value);
  x.value = null;
  return value;
}
/** So is a local `let`'s cell: the fact survives its allocation and its write. */
function keptAcrossLocalCell(x: { value: number | null }): number {
  if (x.value === null) return 0;
  let count = x.value;
  count = x.value;
  return x.value;
}
/** Another parameter may alias `a`, so its write forgets the fact and the read
 * is broad again. TypeScript assumes no aliasing here and claims a number. */
function lostAcrossOtherParameter(
  a: { value: number | null },
  b: { value: number | null },
): number | null {
  if (a.value === null) return 0;
  b.value = null;
  return a.value;
}
