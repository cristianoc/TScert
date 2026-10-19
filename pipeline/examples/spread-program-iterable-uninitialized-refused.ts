// A spread of a program's iterable after a read of a binding a closure may
// read before its initialization: JavaScript throws at the read, before the
// iterator runs (run under Node: the log holds "thrown" alone), where
// collecting before the statement would run the iterator first. Refused.
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

export function early(log: string[]): number {
  const make = (): number[] => [later, ...new Steps(log)];
  try {
    make();
  } catch {
    log.push("thrown");
  }
  const later: number = 1;
  return make().length;
}
