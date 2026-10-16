// JavaScript steps an array pattern's source through the array's iterator,
// which stays finished once a step found the end. Here the hole's step finds
// the empty array's end; the key then grows the array, and the next step still
// finds the iterator finished, so the default writes 9. A read of position 1
// would find 2. Code that may change an array between the steps of a pattern
// over an array another reference may hold is outside the fragment.
export function holeThenGrow(): number {
  const xs: number[] = [];
  const box = { slot: 0 };
  [, box[(xs.push(1, 2), "slot")] = 9] = xs;
  return box.slot;
}
