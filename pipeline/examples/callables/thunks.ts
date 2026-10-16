/** A factory returns a zero-argument closure. Its captured cell is read when
 * the thunk is invoked, after the intervening write. */
function returnedThunk(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  // prettier-ignore
  const factory: () => () => boolean = (): () => boolean => (): boolean => cell.value;
  const thunk = factory();
  cell.value = !seed;
  return thunk();
}

/** A thunk saved from a cell retains its original closure after replacement.
 * The replacement runs only on a later invocation of the newly read thunk. */
function storedThunk(seed: boolean): boolean {
  const slot: { value: () => boolean } = { value: (): boolean => seed };
  const saved = slot.value;
  slot.value = (): boolean => !seed;
  const current = slot.value;
  return saved() ? !current() : current();
}
