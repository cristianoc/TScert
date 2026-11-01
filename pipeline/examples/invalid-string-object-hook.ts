// String(o) can call an own toString method that clears cell.value.
// TypeScript retains the narrowing; under Node, kept returns undefined.
function kept(cell: { value: string | undefined }, o: { a: number }): string {
  if (cell.value === undefined) return "";
  String(o);
  return cell.value;
}
