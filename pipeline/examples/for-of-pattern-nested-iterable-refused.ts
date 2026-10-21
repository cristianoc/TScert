// An array pattern binding a `for...of` over a program's iterable whose
// values are themselves a program's iterables: JavaScript steps each value's
// own iterator, while the pattern reads an array's positions, so the pattern
// is refused where it reads a value that is no array.
class Pair {
  [Symbol.iterator](): Iterator<number> {
    let i = 0;
    return {
      next: (): IteratorResult<number> => {
        const k = i;
        if (k >= 2) return { done: true, value: undefined };
        i = k + 1;
        return { done: false, value: k };
      },
      return: (): IteratorResult<number> => ({ done: true, value: undefined }),
    };
  }
}

class Pairs {
  [Symbol.iterator](): Iterator<Pair> {
    let given = false;
    return {
      next: (): IteratorResult<Pair> => {
        if (given) return { done: true, value: undefined };
        given = true;
        return { done: false, value: new Pair() };
      },
      return: (): IteratorResult<Pair> => ({ done: true, value: undefined }),
    };
  }
}

export function seconds(pairs: Pairs): number {
  let sum = 0;
  for (const [, b] of pairs) sum = sum + b;
  return sum;
}
