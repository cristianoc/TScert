// A spread of an iterable the program defines, `...list`, is the fresh array
// of the values its iterator yields until done: the protocol runs before the
// statement, where nothing it evaluates before the spread can change, and
// closes nothing (a spread steps to the end).
class Cell {
  constructor(
    readonly value: number,
    readonly next: Cell | null,
  ) {}
}

class LinkedList {
  constructor(readonly head: Cell | null) {}
  [Symbol.iterator](): Iterator<number> {
    let node = this.head;
    return {
      next: (): IteratorResult<number> => {
        const current = node;
        if (current === null) return { done: true, value: undefined };
        node = current.next;
        return { done: false, value: current.value };
      },
      return: (): IteratorResult<number> => ({ done: true, value: undefined }),
    };
  }
}

function sum(...xs: number[]): number {
  let total = 0;
  for (const x of xs) total = total + x;
  return total;
}

export function spread(values: Iterable<number>): number {
  return sum(...values);
}

export function spreadAfter(list: LinkedList, first: number): number {
  return sum(first, ...list, 1);
}

export function copy(list: LinkedList): number[] {
  const xs = [...list];
  return xs;
}
