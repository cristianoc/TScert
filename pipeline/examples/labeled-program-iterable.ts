// Labeled jumps out of loops over a program's iterable: `continue outer`
// from the inner loop closes the inner iterator, whose `return` counts in
// `log.closed`, and goes on with the outer one; `break outer` closes both.
class Cell {
  readonly value: number;
  readonly next: Cell | null;
  constructor(value: number, next: Cell | null) {
    this.value = value;
    this.next = next;
  }
}

class LinkedList {
  readonly head: Cell | null;
  readonly log: { closed: number };
  constructor(head: Cell | null, log: { closed: number }) {
    this.head = head;
    this.log = log;
  }
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


// A `continue outer` from the inner loop closes the inner iterator and
// steps the outer one; a `break outer` closes both.
export function nested(outerList: LinkedList, innerList: LinkedList): number {
  let n = 0;
  outer: for (const a of outerList) {
    for (const b of innerList) {
      if (b === a) continue outer;
      if (b > 5) break outer;
      n++;
    }
  }
  return n;
}

export function lists(outerValues: number[], innerValues: number[], log: { closed: number }): [LinkedList, LinkedList] {
  let outerHead: Cell | null = null;
  for (const v of outerValues) outerHead = new Cell(v, outerHead);
  let innerHead: Cell | null = null;
  for (const v of innerValues) innerHead = new Cell(v, innerHead);
  return [new LinkedList(outerHead, log), new LinkedList(innerHead, log)];
}
