// A field target is written at its contract: the string is no number.
function wrong(box: { slot: number }): void {
  // @ts-expect-error Type 'string' is not assignable to type 'number'
  [box.slot] = ["x"];
}
