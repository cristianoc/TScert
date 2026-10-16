// The fresh array a spread collects holds what the iterator yields: strings
// here, which a callee collecting numbers does not take. The iterator states
// no `return`, which a spread never calls.
class Words {
  constructor(readonly words: string[]) {}
  [Symbol.iterator](): { next(): IteratorResult<string> } {
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
    };
  }
}

function sum(...xs: number[]): number {
  return xs.length;
}

export function total(words: Words): number {
  return sum(...words);
}
