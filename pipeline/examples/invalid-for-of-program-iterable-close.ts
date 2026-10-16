// Leaving the loop by `break` calls the iterator's `return` (IteratorClose),
// whose result JavaScript requires to be an object, throwing a TypeError
// otherwise: this one's is declared a number, which the close's call does
// not take as an object.
interface Counter {
  next(): IteratorResult<number>;
  return(): number;
}

class Countdown {
  constructor(readonly from: number) {}
  [Symbol.iterator](): Counter {
    let n = this.from;
    return {
      next: (): IteratorResult<number> => {
        const current = n;
        n = current - 1;
        return current <= 0
          ? { done: true, value: undefined }
          : { done: false, value: current };
      },
      return: (): number => 0,
    };
  }
}

export function firstEven(c: Countdown): number {
  let found = -1;
  for (const v of c) {
    if (v % 2 === 0) {
      found = v;
      break;
    }
  }
  return found;
}
