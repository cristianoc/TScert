// A guarded clause freed by a conditional's test, pretext's
// `getItemTabAdvance` in `line-break.ts`: each nullable parallel array is
// read at `index` in the arm where its own null test failed. The test frees
// the guard (ARITHMETIC.md, "Guarded clauses"), and the arm's read of
// the same path again, which a read link of the test's read answers, states
// the freed length of the read's value; the producer claims the read below
// the length from the same freed fact.

export type Items = {
  tabStopAdvances: number[] | null;
  minimumTabAdvances: number[] | null;
  insideExtras: number[] | null;
};

/**
 * @requires safeInteger(index) && 0 <= index && index < widths.length
 * @requires items.tabStopAdvances === null || index < items.tabStopAdvances.length
 * @requires items.minimumTabAdvances === null || index < items.minimumTabAdvances.length
 * @requires items.insideExtras === null || index < items.insideExtras.length
 */
export function itemAdvance(widths: number[], items: Items, index: number, tabStop: number): number {
  const stopAdvance = items.tabStopAdvances === null ? tabStop : items.tabStopAdvances[index]!;
  const minimumAdvance = items.minimumTabAdvances === null ? 0 : items.minimumTabAdvances[index]!;
  const endEdge = items.insideExtras === null ? 0 : items.insideExtras[index]! / 2;
  return stopAdvance + minimumAdvance - endEdge + widths[index]!;
}

/**
 * @requires safeInteger(index) && 0 <= index
 * @requires items.insideExtras === null || index < items.insideExtras.length
 */
export function extraUnlessNull(items: Items, index: number): number {
  return items.insideExtras !== null ? items.insideExtras[index]! : 0;
}
