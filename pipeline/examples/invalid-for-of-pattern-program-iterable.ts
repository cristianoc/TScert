// A pattern binding a `for...of` over a program's iterable reads each
// yielded array by position: a position past a short array is `undefined`,
// which TypeScript types as the element (tests/node-runs.mts runs `second`,
// which returns `undefined`).
class Row {
  readonly cells: number[];
  readonly next: Row | null;
  constructor(cells: number[], next: Row | null) {
    this.cells = cells;
    this.next = next;
  }
}

class Rows {
  readonly head: Row | null;
  constructor(head: Row | null) {
    this.head = head;
  }
  [Symbol.iterator](): Iterator<number[]> {
    let node = this.head;
    return {
      next: (): IteratorResult<number[]> => {
        const current = node;
        if (current === null) return { done: true, value: undefined };
        node = current.next;
        return { done: false, value: current.cells };
      },
      return: (): IteratorResult<number[]> => ({
        done: true,
        value: undefined,
      }),
    };
  }
}

export function second(rows: Rows): number {
  for (const [, b] of rows) return b;
  return 0;
}
