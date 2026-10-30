// `Array.from(s, f)` calls `f`, which may write anything the string is not:
// a field narrowed before the call is read again after it at its declared
// type (run under Node: `undefined`). TypeScript keeps the narrowing.
export function kept(
  cell: { value: string | undefined },
  word: string,
): string {
  if (cell.value === undefined) return "";
  Array.from(word, (c) => ((cell.value = undefined), c));
  return cell.value;
}
