// An array pattern over an iterable the program defines steps its iterator
// once per element (a hole too), the rest to the end; a pattern without a
// rest closes the iterator when it is not done. A name bound past the end
// is `undefined`.
class Cell {
  constructor(
    readonly value: number,
    readonly next: Cell | null,
  ) {}
}

class LinkedList {
  constructor(
    readonly head: Cell | null,
    readonly log: { closed: number },
  ) {}
  [Symbol.iterator](): Iterator<number> {
    let node = this.head;
    const log = this.log;
    return {
      next: (): IteratorResult<number> => {
        const current = node;
        if (current === null) return { done: true, value: undefined };
        node = current.next;
        return { done: false, value: current.value };
      },
      return: (): IteratorResult<number> => {
        log.closed = log.closed + 1;
        return { done: true, value: undefined };
      },
    };
  }
}

export function firstAndThird(list: LinkedList): number {
  const [a, , c] = list;
  if (a === undefined || c === undefined) return 0;
  return a + c;
}

export function tail(list: LinkedList): number[] {
  const [head, ...rest] = list;
  return head === undefined ? [] : rest;
}

export function only(values: Iterable<string>): string {
  const [first] = values;
  return first ?? "";
}
