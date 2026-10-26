// A class whose `cause` is an accessor: `Error` runs its getter through
// `[[Get]]`, client code that shrinks the array `map` visits. Refused at the
// accessor.
class Options {
  readonly xs: string[];
  constructor(xs: string[]) {
    this.xs = xs;
  }
  get cause(): number {
    this.xs.pop();
    return 0;
  }
}
export function wrong(xs: string[]): string[] {
  const options = new Options(xs);
  return xs.map((x) => Error(x, options).message);
}
