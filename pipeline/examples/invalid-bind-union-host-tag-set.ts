class Steps {
  next(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
}

class Source {
  readonly iterator: Steps | 1 | 2;
  constructor(iterator: Steps | 1 | 2) {
    this.iterator = iterator;
  }
  [Symbol.iterator](): Steps | 1 | 2 {
    return this.iterator;
  }
}

export function first(source: Source): number {
  for (const value of source) return value;
  return 0;
}
