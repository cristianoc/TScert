class A {
  next(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
  return(): IteratorResult<number, undefined> {
    return { done: true, value: undefined };
  }
}

class B {
  next(): IteratorResult<number, string> {
    return { done: true, value: "finished" };
  }
  return(): IteratorResult<number, string> {
    return { done: true, value: "closed" };
  }
}

class Source {
  readonly iterator: A | B | undefined;
  constructor(iterator: A | B | undefined) {
    this.iterator = iterator;
  }
  [Symbol.iterator](): A | B | undefined {
    return this.iterator;
  }
}

export function first(source: Source): number {
  for (const value of source) return value;
  return 0;
}
