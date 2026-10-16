/**
 * An `instanceof` test of a constructor passed in: nothing in the file says
 * which prototype it gives its instances, so the test is not lowered; one of
 * a class the file declares is (DESIGN.md, "Guards").
 */
function describe(
  x: { a: number } | number,
  C: new () => { a: number },
): string {
  if (x instanceof C) {
    return "made by C";
  }
  return "something else";
}
