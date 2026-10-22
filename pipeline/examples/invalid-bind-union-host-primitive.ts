class Steps {
  next(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
}

class Source {
  readonly iterator: Steps | number;
  constructor(iterator: Steps | number) {
    this.iterator = iterator;
  }
  [Symbol.iterator](): Steps | number {
    return this.iterator;
  }
}

export function first(source: Source): number {
  for (const value of source) return value;
  return 0;
}
