// A `for...of` loop over an array inside a counter loop's body: the array
// iterator is allocated apart from every array's store, and its step changes
// only its own locations (`call-own`), so the counter's bound by the outer
// array's length survives the inner loop (PROGRAM-TYPING.md, "Linear facts").

export function nested(units: number[], xs: number[]): number {
  let s = 0;
  for (let i = 0; i < units.length; i++) {
    s = s + units[i]!;
    for (const x of xs) s = s + x;
    s = s + units[i]!;
  }
  return s;
}
