// One host of the union declares `next` with a required parameter: the
// protocol calls it with none, so `start` is `undefined` and the loop's
// first value is `undefined`, which TypeScript types as a number
// (tests/node-runs.mts runs `first`, which returns `undefined`). The hosts'
// members take different parameters: no one bound signature is either's.
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

class From {
  started: boolean;
  constructor() {
    this.started = false;
  }
  next(start: number): IteratorResult<number, undefined> {
    if (this.started) return { done: true, value: undefined };
    this.started = true;
    return { done: false, value: start };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): From {
    return this;
  }
}

export function first(it: Countdown | From): number {
  for (const v of it) return v;
  return 0;
}
