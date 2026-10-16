// TypeScript keeps `cell.value` narrowed across the call, but the call writes
// null there: a call between the test and the return reads anew.
export function cleared(): boolean {
  const cell: { value: boolean | null } = { value: true };
  const clear = (): void => {
    cell.value = null;
  };
  if (cell.value !== null) {
    clear();
    return cell.value;
  }
  return false;
}
