// One host's `next` returns a number, not an iterator result. JavaScript's
// IteratorStepValue throws a TypeError on it; the protocol's reads of
// `done` and `value` on a number would give `undefined`, which the loop
// binds where TypeScript says a number (tests/node-runs.mts runs `first`,
// which throws). The step's result has no `done` to read.
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

class Bare {
  next(): number {
    return 1;
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Bare {
    return this;
  }
}

export function first(it: Countdown | Bare): number {
  for (const v of it) return v;
  return 0;
}
