// A spread of a program's iterable as an argument of a call of a function
// the file only declares (`declare function`): at run time the global may be
// a getter, which runs before the iterator in the source (run under Node:
// the log holds "getter", then "iterator"). An ambient declaration says
// nothing of what the name holds, so the collection is not placed before the
// statement.
declare function counted(...xs: number[]): number;

class Steps {
  readonly log: string[];
  constructor(log: string[]) {
    this.log = log;
  }
  [Symbol.iterator](): Iterator<number> {
    const log = this.log;
    return {
      next: (): IteratorResult<number> => {
        log.push("iterator");
        return { done: true, value: undefined };
      },
      return: (): IteratorResult<number> => ({ done: true, value: undefined }),
    };
  }
}

export function call(log: string[]): number {
  return counted(...new Steps(log));
}
