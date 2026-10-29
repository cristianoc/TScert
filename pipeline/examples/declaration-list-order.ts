// A declaration list runs its declarators in order: the iterator steps and
// the close of the first declarator's pattern over an iterable the program
// defines, then the second declarator's initializer, which writes the same
// log, then a default reading the bindings of both. Under Node,
// `order(new Steps([]))` returns "next,return,second:s,s3".
class Steps {
  constructor(readonly log: string[]) {}
  [Symbol.iterator](): Iterator<string> {
    const log = this.log;
    return {
      next: (): IteratorResult<string> => {
        log.push("next");
        return { done: false, value: "s" };
      },
      return: (): IteratorResult<string> => {
        log.push("return");
        return { done: true, value: undefined };
      },
    };
  }
}

function note(log: string[], text: string): Within<{ value: "any"; store: "grow" }, number> {
  log.push(text);
  return log.length;
}

export function order(steps: Steps): string {
  const log = steps.log;
  const [first] = steps, count = note(log, `second:${first ?? ""}`), [both = `${first ?? ""}${count}`] = [undefined];
  return `${log.join(",")},${both}`;
}
