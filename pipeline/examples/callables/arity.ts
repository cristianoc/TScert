/** A multi-argument call must select its callee first, then evaluate arguments
 * left to right, then enter the body. The expected result is true: the first
 * argument observes true, the second false, and the body observes true again.
 * Reordering arguments or running the body before the second argument changes
 * the result. The source pipeline checks this through native argument lists. */
function argumentOrder(): boolean {
  const cell: { value: boolean } = { value: false };
  // prettier-ignore
  const choose: () => (first: boolean, second: boolean) => boolean =
    (): (first: boolean, second: boolean) => boolean => {
      cell.value = true;
      return (first: boolean, second: boolean): boolean => first && !second && cell.value;
    };
  const first: () => boolean = (): boolean => {
    const old: boolean = cell.value;
    cell.value = false;
    return old;
  };
  const second: () => boolean = (): boolean => {
    const old: boolean = cell.value;
    cell.value = true;
    return old;
  };
  return choose()(first(), second());
}

/** A nested native call returns a closure capturing its second parameter and
 * an outer binding; those slots must survive both parameter environments. */
function capturedParameters(seed: boolean): boolean {
  // prettier-ignore
  const factory: (unit: null, flag: boolean) => (next: boolean) => boolean =
    (unit: null, flag: boolean): (next: boolean) => boolean =>
      (next: boolean): boolean => flag ? seed : next;
  const run: (flag: boolean) => boolean = (flag: boolean): boolean =>
    factory(null, flag)(seed);
  return run(!seed);
}

/** Union elimination must keep both actuals fixed while changing the callee's
 * type, and retain the result admitted by each alternative. */
function unionArguments(
  f:
    | ((unit: null, flag: true) => true)
    | ((unit: null, flag: boolean) => boolean),
): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => f(unit, true);
  return run(null);
}
