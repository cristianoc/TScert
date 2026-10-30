// A call of a member read through `!` passes the member's object as its
// receiver, which must meet the function's `this` parameter: an object
// without `k` is no `Keyed`.
interface Keyed {
  readonly k: number;
}
interface Loose {
  readonly read: (this: Keyed) => number;
}

function current(o: Loose): Loose {
  return o;
}

export function wrong(o: Loose): number {
  return current(o).read!();
}
