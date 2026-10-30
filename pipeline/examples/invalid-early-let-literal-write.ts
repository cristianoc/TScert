// A closure reading a `let` declared after it, unannotated and initialized
// by a number literal, the `let` then assigned a string, which TypeScript
// rejects (TS2322): the cell's contract is the widened literal, `number`, so
// the write is refused. Under Node `late` returns the string.
export function late(): number {
  const read = (): number => start;
  let start = -1;
  // @ts-expect-error a string is no number
  start = "late";
  return read();
}
