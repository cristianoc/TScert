// A linked list the program defines, iterated by the iterator protocol:
// `[Symbol.iterator]()` gives an iterator whose `next` steps the cells and
// whose `return` counts the closes in `log.closed`. A `for...of` over it
// calls `return` when it is left early (`break`, `return`, a throw out of
// the body), and not when it runs to its end or `continue`s (test.mts runs
// these functions and reads the count).
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

// An iterator that is a class instance: its `next` and `return` are methods
// of its prototype, each read bound to the iterator.
class Countdown {
  left: number;
  readonly log: { closed: number };
  constructor(left: number, log: { closed: number }) {
    this.left = left;
    this.log = log;
  }
  next(): IteratorResult<number> {
    const n = this.left;
    if (n <= 0) return { done: true, value: undefined };
    this.left = n - 1;
    return { done: false, value: n };
  }
  return(): IteratorResult<number> {
    this.log.closed = this.log.closed + 1;
    return { done: true, value: undefined };
  }
}

class Countdowns {
  readonly from: number;
  readonly log: { closed: number };
  constructor(from: number, log: { closed: number }) {
    this.from = from;
    this.log = log;
  }
  [Symbol.iterator](): Countdown {
    return new Countdown(this.from, this.log);
  }
}

// An iterator whose `return` throws: a throw out of the loop's body is the
// one that leaves, the close's own discarded.
class Brittle {
  [Symbol.iterator](): Iterator<number> {
    return {
      next: (): IteratorResult<number> => ({ done: false, value: 0 }),
      return: (): IteratorResult<number> => {
        throw new Error("close");
      },
    };
  }
}

export function sum(list: LinkedList): number {
  let total = 0;
  for (const v of list) total = total + v;
  return total;
}

// `break`: the iterator's `return` runs, then the loop is left.
export function firstAbove(list: LinkedList, limit: number): number {
  let found = -1;
  for (const v of list) {
    if (v > limit) {
      found = v;
      break;
    }
  }
  return found;
}

// `return` from the body: the value is held while the iterator closes.
export function firstOver(list: LinkedList, limit: number): number {
  for (const v of list) {
    if (v > limit) return v;
  }
  return -1;
}

export function skipSmall(list: LinkedList, limit: number): number {
  let total = 0;
  for (const v of list) {
    if (v < limit) continue;
    total = total + v;
  }
  return total;
}

export function nested(a: LinkedList, b: LinkedList): number {
  let count = 0;
  for (const x of a) {
    for (const y of b) {
      if (x === y) break;
      count = count + 1;
    }
  }
  return count;
}

export function firstEven(c: Countdowns): number {
  for (const v of c) {
    if (v % 2 === 0) return v;
  }
  return 0;
}

// A throw out of the body closes the iterator, whose own throw is dropped:
// what the handler catches is the body's error.
export function bodyThrows(list: Brittle): unknown {
  try {
    for (const v of list) {
      if (v === 0) throw new Error("body");
    }
    return "done";
  } catch (e) {
    return e;
  }
}
