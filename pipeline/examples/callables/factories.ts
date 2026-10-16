/**
 * Each factory invocation allocates a private cell. Calls return the old value
 * while storing the new one, so these observations are false, false, true.
 */
function factoryInstances(): boolean {
  // prettier-ignore
  const make: (unit: null) => (next: boolean) => boolean = (
    unit: null,
  ): (next: boolean) => boolean => {
    const cell: { value: boolean } = { value: false };
    return (next: boolean): boolean => {
      const old: boolean = cell.value;
      cell.value = next;
      return old;
    };
  };
  const first = make(null);
  const second = make(null);
  const a: boolean = first(true);
  const b: boolean = second(false);
  const c: boolean = first(false);
  return a ? false : b ? false : c;
}

/**
 * Hoisting the cell makes the otherwise identical factory share state.
 * Distinct returned closures observe false, true, false through the same cell.
 */
function sharedFactoryInstances(): boolean {
  const cell: { value: boolean } = { value: false };
  // prettier-ignore
  const make: (unit: null) => (next: boolean) => boolean = (
    unit: null,
  ): (next: boolean) => boolean => {
    return (next: boolean): boolean => {
      const old: boolean = cell.value;
      cell.value = next;
      return old;
    };
  };
  const first = make(null);
  const second = make(null);
  const a: boolean = first(true);
  const b: boolean = second(false);
  const c: boolean = first(false);
  return a ? false : b ? false : c;
}
