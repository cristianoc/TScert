// One host's `next` declares its receiver another type, `this: Seed`; the
// protocol calls it on the iterator, a `Borrowed`, whose `seed` is not
// there, so the loop's value is `undefined` where TypeScript says a number
// (tests/node-runs.mts runs `first`, which returns `undefined`). The
// iterator is not within the member's receiver.
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

interface Seed {
  readonly seed: number;
}

class Borrowed {
  next(this: Seed): IteratorResult<number, undefined> {
    return { done: false, value: this.seed };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Borrowed {
    return this;
  }
}

export function first(it: Countdown | Borrowed): number {
  for (const v of it) return v;
  return 0;
}
