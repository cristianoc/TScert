/**
 * Pass a Boolean through a unary callback. Its argument and result contracts
 * cover both true and false.
 */
function booleanIdentity(seed: boolean): boolean {
  const identity: (value: boolean) => boolean = (value: boolean): boolean =>
    value;
  return identity(seed);
}

/**
 * Pass any null-or-Boolean value through a callback. This exercises primitive
 * unions in both the arrow domain and codomain.
 */
function unionIdentity(seed: null | boolean): null | boolean {
  const identity: (value: null | boolean) => null | boolean = (
    value: null | boolean,
  ): null | boolean => value;
  return identity(seed);
}

/**
 * Pass a Boolean argument to a callback that writes its captured cell. The
 * null call result is bound explicitly, and the later read returns false.
 */
function capturedWriter(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const write: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  const done: null = write(false);
  return cell.value;
}

/**
 * Assign a function accepting any Boolean and returning true to a contract
 * accepting only true and returning Boolean. This exercises contravariance of
 * arguments and covariance of results.
 */
function narrowerCallContract(): boolean {
  const acceptTrue: (value: true) => boolean = (value: boolean): true => true;
  return acceptTrue(true);
}

/**
 * Return a closure that writes and reads its retained cell. Each later call
 * returns the argument it just stored.
 */
function returnedWriter(): (next: boolean) => boolean {
  const cell: { value: boolean } = { value: true };
  return (next: boolean): boolean => {
    cell.value = next;
    return cell.value;
  };
}

/**
 * Save an immutable snapshot before calling a writer. Refining that snapshot
 * remains valid after the cell changes, so every path returns true.
 */
function stableSnapshot(seed: boolean): true {
  const cell: { value: boolean } = { value: seed };
  const reset: (next: boolean) => null = (next: boolean): null => {
    cell.value = next;
    return null;
  };
  const snapshot: boolean = cell.value;
  if (snapshot) {
    const done: null = reset(false);
    return snapshot;
  }
  return true;
}
