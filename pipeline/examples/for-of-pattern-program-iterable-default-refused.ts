// A default in a pattern binding a `for...of` over a program's iterable that
// writes the yielded array, which the iterator keeps a reference to:
// JavaScript steps the array's iterator, which stays finished once a step
// found the end, so after `grow` refills the empty array `b` is `undefined`
// (tests/node-runs.mts runs `grown`), while reading position 1 would see 2.
function grow(xs: number[]): number {
  xs.push(1, 2);
  return 0;
}

class Shared {
  readonly row: number[];
  constructor(row: number[]) {
    this.row = row;
  }
  [Symbol.iterator](): Iterator<number[]> {
    let done = false;
    const row = this.row;
    return {
      next: (): IteratorResult<number[]> => {
        if (done) return { done: true, value: undefined };
        done = true;
        return { done: false, value: row };
      },
      return: (): IteratorResult<number[]> => ({
        done: true,
        value: undefined,
      }),
    };
  }
}

export function grown(shared: Shared): number[] {
  const out: number[] = [];
  for (const [a = grow(shared.row), b] of shared) out.push(a, b);
  return out;
}
