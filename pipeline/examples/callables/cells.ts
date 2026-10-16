/** Saving a callback before replacement preserves that value, while a later
 * cell read obtains the replacement. Both calls retain their own captures. */
function replacedCallback(seed: boolean): boolean {
  const slot: { value: (next: boolean) => boolean } = {
    value: (next: boolean): boolean => seed,
  };
  const saved = slot.value;
  slot.value = (next: boolean): boolean => !seed;
  const current = slot.value;
  const old: boolean = saved(false);
  const fresh: boolean = current(false);
  return old ? !fresh : fresh;
}

/** Recursion is tied through a local cell. Reading the installed callback at
 * invocation time reaches the base case, rather than the initial callback. */
function recursiveCallback(seed: boolean): boolean {
  const slot: { value: (again: boolean) => boolean } = {
    value: (again: boolean): boolean => !seed,
  };
  slot.value = (again: boolean): boolean => {
    const callback = slot.value;
    return again ? callback(false) : seed;
  };
  const start = slot.value;
  return start(true);
}
