// An async method's promise settles to what its body returns, which must
// meet the annotation's: here a string where a number is promised.
class Counter {
  label: string = "c";
  async next(): Promise<number> {
    // @ts-expect-error a string is not a number
    return this.label;
  }
}

export function make(): Counter {
  return new Counter();
}
