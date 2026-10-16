/**
 * A locally checked callback crosses an argument boundary. The invoking closure
 * supplies true; the callback mutates its captured cell and returns its old value.
 */
function callableArgument(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const exchange: (next: boolean) => boolean = (next: boolean): boolean => {
    const old: boolean = cell.value;
    cell.value = next;
    return old;
  };
  const invoke: (f: (next: boolean) => boolean) => boolean = (
    f: (next: boolean) => boolean,
  ): boolean => f(true);
  const old: boolean = invoke(exchange);
  return old ? cell.value : false;
}

/**
 * A callback parameter escapes inside a returned wrapper, then crosses another
 * argument boundary. The eventual call must forward its argument and observe
 * the captured cell after the intervening write, not at wrapper creation.
 */
function escapedCallbackArgument(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const exchange: (next: boolean) => boolean = (next: boolean): boolean => {
    const old: boolean = cell.value;
    cell.value = next;
    return old;
  };
  // prettier-ignore
  const wrap: (f: (next: boolean) => boolean) => (next: boolean) => boolean =
    (f: (next: boolean) => boolean): (next: boolean) => boolean =>
      (next: boolean): boolean => f(next);
  const invoke: (f: (next: boolean) => boolean) => boolean = (
    f: (next: boolean) => boolean,
  ): boolean => f(seed);
  const wrapped = wrap(exchange);
  cell.value = !seed;
  const old: boolean = invoke(wrapped);
  return old;
}

/**
 * Multi-argument functions cross an invariant cell boundary and escape through
 * a narrower first-parameter contract. The second parameter must remain null.
 */
function exchangeMultiArgument(
  initial: (flag: boolean, marker: null) => boolean,
  replacement: (flag: boolean, marker: null) => boolean,
): (flag: true, marker: null) => boolean {
  const cell: { value: (flag: boolean, marker: null) => boolean } = {
    value: initial,
  };
  const old: (flag: boolean, marker: null) => boolean = cell.value;
  cell.value = replacement;
  return old;
}
