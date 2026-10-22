// The iterator protocol over a union of iterables: GetIterator gives a union
// of iterators, and `next` (and `return`) is bound to whichever the iterator
// is, `%iterator.next.bind(%iterator)`, a member bound to a union of hosts.
// The bound function takes what every host's member takes and returns the
// union of their results: two `IteratorResult`s, each with its own
// `TReturn`, of which the loop reads the not-done arms' values.
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
    this.left = 0;
    return { done: true, value: undefined };
  }
  [Symbol.iterator](): Countdown {
    return this;
  }
}

// An iterator whose return value is a string: its `done` result's value.
class Repeat {
  times: number;
  readonly value: number;
  constructor(times: number, value: number) {
    this.times = times;
    this.value = value;
  }
  next(): IteratorResult<number, string> {
    const t = this.times;
    if (t <= 0) return { done: true, value: "finished" };
    this.times = t - 1;
    return { done: false, value: this.value };
  }
  return(): IteratorResult<number, string> {
    this.times = 0;
    return { done: true, value: "closed" };
  }
  [Symbol.iterator](): Repeat {
    return this;
  }
}

type Steps = Countdown | Repeat;

// Nullable hosts are narrowed before GetIterator reads the method.
export function nullable(it: Steps | null | undefined): number {
  if (it === null) return 0;
  if (it === undefined) return 0;
  let sum = 0;
  for (const v of it) sum = sum + v;
  return sum;
}
