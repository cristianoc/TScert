// Iterators whose `next` is a field holding a function, not a method: a
// field read gives the function, bound by the protocol to the iterator.
// Over a union of two such records, the bound target is either record's
// function, which is no member of its host: no rule binds a union of
// callables, so the loop is refused at the bind.
interface Ones {
  readonly next: () => IteratorResult<number, undefined>;
  readonly return: () => IteratorResult<number, undefined>;
}

interface Twos {
  readonly next: () => IteratorResult<number, string>;
  readonly return: () => IteratorResult<number, string>;
}

class Source {
  readonly it: Ones | Twos;
  constructor(it: Ones | Twos) {
    this.it = it;
  }
  [Symbol.iterator](): Ones | Twos {
    return this.it;
  }
}

export function total(s: Source): number {
  let sum = 0;
  for (const v of s) sum = sum + v;
  return sum;
}
