// Classes declared in a function's block: each call creates them again,
// their methods reading the call's bindings; a derived one extends a base
// of the same block, and `instanceof` narrows a name it holds for. Run under
// Node: an instance of an earlier call's class is no instance of a later
// call's; so is one of an earlier loop iteration's, and a call operand runs once.
export function count(items: readonly string[], prefix: string): number {
  class Counter {
    total: number;
    constructor(start: number) {
      this.total = start;
    }
    label(item: string): string {
      return prefix + item;
    }
  }
  class Long extends Counter {
    readonly limit: number = 3;
  }
  const counter = new Long(0);
  let sum = 0;
  for (const item of items) sum += counter.label(item).length > counter.limit ? 1 : 0;
  const held: Counter | number = items.length ? counter : 0;
  if (held instanceof Counter) return held.total + sum;
  return sum;
}

export function fresh(previous: unknown): { made: object; same: boolean } {
  class Token {}
  return { made: new Token(), same: previous instanceof Token };
}

export function rounds(n: number): number {
  let previous: unknown = null;
  let matched = 0;
  for (let i = 0; i < n; i++) {
    class Round {}
    if (previous instanceof Round) matched += 1;
    previous = new Round();
  }
  return matched;
}

export function once(): number {
  let calls = 0;
  class Probe {}
  const next = (): unknown => {
    calls += 1;
    return new Probe();
  };
  return next() instanceof Probe ? calls : -1;
}
