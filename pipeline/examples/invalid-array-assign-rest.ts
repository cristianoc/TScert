// An assigned rest is written to its local at the local's contract.
export function restContract(): void {
  let x: number = 0;
  let r: string[] = [];
  [x, ...r] = [1, 2, 3];
}
