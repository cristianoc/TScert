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

// The protocol over a union of iterables: `next` and `return` each bound to
// whichever iterator GetIterator gave; the values are the yields' `number`.
export function total(it: Steps): number {
  let sum = 0;
  for (const v of it) sum = sum + v;
  return sum;
}

// `break` closes the iterator through its `return`, bound the same way.
export function firstOver(it: Countdown | Repeat, limit: number): number {
  let found = -1;
  for (const v of it) {
    if (v > limit) {
      found = v;
      break;
    }
  }
  return found;
}

// The protocol in a closure's body.
export function later(it: Steps): () => number {
  return (): number => {
    let sum = 0;
    for (const v of it) sum = sum + v;
    return sum;
  };
}

// A union of a set and a readonly set: the spread runs the protocol over a
// `SetIterator` or the overlay's `Iterator`, its `next` bound to whichever.
export function merged(
  bound: ReadonlySet<string> | Set<string>,
  more: readonly string[],
): number {
  return new Set([...bound, ...more]).size;
}

// An alias nested in a union: the host's labels, not the spelling, split.
export function nestedAlias(it: Steps | Countdown): number {
  let sum = 0;
  for (const v of it) sum = sum + v;
  return sum;
}

// One host: its member bound to it, returning its own result.
export function countdown(it: Countdown): number {
  let sum = 0;
  for (const v of it) sum = sum + v;
  return sum;
}
