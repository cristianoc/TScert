// The iterator's `next` pops the array a length test guarded before the
// loop: after the loop the array may be empty, so `xs[0]` may be undefined
// where a number is returned.
class Draining {
  constructor(readonly items: number[]) {}
  [Symbol.iterator](): Iterator<number> {
    const items = this.items;
    return {
      next: (): IteratorResult<number> => {
        const v = items.pop();
        return v === undefined ? { done: true, value: undefined } : { done: false, value: v };
      },
    };
  }
}
export function wrong(xs: number[]): number {
  if (xs.length < 1) return 0;
  let n = 0;
  for (const v of new Draining(xs)) n = n + v;
  return xs[0];
}
