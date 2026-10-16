// A module function's rest typed by its own type parameter: each call
// instantiates the parameter at the list it collects, within the parameter's
// bound, and the body sees the fresh array at that bound.
function total<T extends readonly number[]>(...args: T): number {
  let sum = 0;
  for (const n of args) sum += n;
  return sum;
}

function view<T extends ReadonlyArray<number>>(
  ...args: T
): ReadonlyArray<number> {
  return args;
}

// A mutable bound: the array is fresh, so the body may write it.
function grown<T extends string[]>(...items: T): string[] {
  items.push("end");
  return items;
}

// A tuple bound: the calls write its positions.
function pair<T extends readonly [string, number]>(...entry: T): string {
  return entry[0];
}

// Fixed parameters before the pack.
function tagged<T extends readonly boolean[]>(
  tag: string,
  ...flags: T
): number {
  return flags.length + tag.length;
}

export function use(flag: boolean): number {
  const v = view(1, 2, 3);
  const g = grown("a", "b");
  const p = pair("k", 1);
  return (
    total(1, 2) +
    total() +
    v.length +
    g.length +
    p.length +
    tagged("t", flag, !flag)
  );
}
