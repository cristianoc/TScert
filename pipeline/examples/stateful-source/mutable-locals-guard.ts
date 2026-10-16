// Creating a zero-argument closure preserves the established cell contents;
// calling it later observes the replacement through its own null guard.
function guardedMutableRead(): boolean {
  let value: boolean | null = null;
  value = true;
  const read = (): boolean => {
    if (value !== null) {
      return value;
    }
    return false;
  };
  value = null;
  return read();
}
