// The iterator's `next` yields strings: the loop's element is a string,
// which the sum does not take as a number.
class Words {
  constructor(readonly words: string[]) {}
  [Symbol.iterator](): Iterator<string> {
    let index = 0;
    const words = this.words;
    return {
      next: (): IteratorResult<string> => {
        const i = index;
        index = i + 1;
        const word = words.at(i);
        return word === undefined
          ? { done: true, value: undefined }
          : { done: false, value: word };
      },
      return: (): IteratorResult<string> => ({ done: true, value: undefined }),
    };
  }
}

export function total(words: Words): number {
  let sum = 0;
  for (const w of words) {
    sum = sum + w;
  }
  return sum;
}
