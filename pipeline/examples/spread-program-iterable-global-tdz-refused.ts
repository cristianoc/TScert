// A spread of a program's iterable after a global the file only declares
// (`declare const`), which at run time may be a lexical binding of another
// script read before its initialization: the read throws before the iterator runs (run under
// Node: the log holds "thrown" alone). The collection is not placed before
// the statement.
declare const late: number;

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

export function read(log: string[]): number[] {
  return [late, ...new Steps(log)];
}
