// One host's `next` is overloaded: `next()` declares number values, while
// its implementation, which TypeScript checks against the overloads only
// loosely, yields a string when called with no argument. The protocol calls
// `next()`, so the loop's value is "s" (tests/node-runs.mts runs `first`,
// which returns "s" despite its number contract).
class Countdown {
  left: number;
  constructor(left: number) {
    this.left = left;
  }
  next(): IteratorResult<number, undefined> {
    const n = this.left;
    if (n <= 0) return { done: true, value: undefined };
    this.left = n - 1;
    return { done: false, value: n };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Countdown {
    return this;
  }
}

class Mixed {
  next(): IteratorResult<number, undefined>;
  next(skip: number): IteratorResult<string, undefined>;
  next(skip?: number): IteratorResult<number | string, undefined> {
    return skip === undefined
      ? { done: false, value: "s" }
      : { done: false, value: skip };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Mixed {
    return this;
  }
}

export function first(it: Countdown | Mixed): number {
  for (const v of it) return v;
  return 0;
}
