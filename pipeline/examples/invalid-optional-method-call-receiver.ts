// The saved object is the call's receiver, which must meet the method's
// `this` parameter: an object without `k` is no `Keyed`.
interface Keyed {
  readonly k: number;
}
interface Loose {
  readonly read?: (this: Keyed) => number;
}

function current(o: Loose): Loose {
  return o;
}

export function wrong(o: Loose): number | undefined {
  return current(o).read?.();
}
