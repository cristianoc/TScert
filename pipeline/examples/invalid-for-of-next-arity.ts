// An iterator whose `next` declares a required parameter: the protocol
// calls it with none, so `start` is `undefined` and the loop's first value
// is `undefined`, which TypeScript types as a number (tests/node-runs.mts
// runs `first`, which returns `undefined`). The bound `next` takes a
// number, and the step's call passes nothing.
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

export function first(it: From): number {
  for (const v of it) return v;
  return 0;
}
