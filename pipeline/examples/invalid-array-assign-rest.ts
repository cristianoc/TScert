// An assigned rest is written to its local at the local's contract.
// On the single pass, a gap: the single pass refuses the array rest over an
// array of unknown length (a stated restriction) before the assignment.
export function restContract(): void {
  let x: number = 0;
  let r: string[] = [];
  [x, ...r] = [1, 2, 3];
}
