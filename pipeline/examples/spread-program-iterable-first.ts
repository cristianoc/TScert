// A spread of a program's iterable that is the first evaluation of its
// statement able to run code: the first element of an array literal before
// others, an argument of a construction of a name, the receiver of a method
// call. Its protocol runs before the statement, where JavaScript runs it, and
// the later operands after it (run under Node: the iterator's log precedes
// the later element's).
class Counter {
  readonly log: string[];
  readonly limit: number;
  constructor(log: string[], limit: number) {
    this.log = log;
    this.limit = limit;
  }
  [Symbol.iterator](): Iterator<number> {
    let n = 0;
    const log = this.log;
    const limit = this.limit;
    return {
      next: (): IteratorResult<number> => {
        log.push("step");
        if (n >= limit) return { done: true, value: undefined };
        n = n + 1;
        return { done: false, value: n };
      },
      return: (): IteratorResult<number> => ({ done: true, value: undefined }),
    };
  }
}

function later(log: string[]): number {
  log.push("later");
  return 0;
}

export function before(c: Counter): number[] {
  return [...c, later(c.log)];
}

export function distinct(c: Counter, more: readonly number[]): Set<number> {
  const all = new Set([...c, ...more]);
  return all;
}

export function doubled(c: Counter): number[] {
  return [...c].map((x) => x * 2);
}
