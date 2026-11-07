// A for...of loop whose body pops the counter loop's array: the inner loop's
// body is no iterator step, so its call takes the length away. Under Node,
// `nestedPop([1, 2, 3], [0])` reads `units[1]` of `[1]`, `undefined` at
// `number`, and answers `NaN`.

export function nestedPop(units: number[], xs: number[]): number {
  let s = 0;
  for (let i = 0; i < units.length; i++) {
    for (const x of xs) {
      units.pop();
      s = s + x;
    }
    s = s + units[i]!;
  }
  return s;
}
