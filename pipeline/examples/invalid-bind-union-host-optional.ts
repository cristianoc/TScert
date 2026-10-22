// One host declares `next` optional and lacks it: GetIterator's read of
// `next` gives `undefined`, and the first step throws a TypeError
// (tests/node-runs.mts runs `first`, which throws). A host whose `next` may
// be absent is not one whose member the bind can take.
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

class Maybe {
  next?(): IteratorResult<number, undefined>;
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Maybe {
    return this;
  }
}

export function first(it: Countdown | Maybe): number {
  for (const v of it) return v;
  return 0;
}
