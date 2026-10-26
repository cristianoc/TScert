// Options typed without `cause` passed through an implicit constructor, which
// forwards them to `Error`: they may own a getter there, which `[[Get]]`
// runs, client code that shrinks the array `map` visits. Refused at the
// options.
class Failure extends Error {}
export function wrong(xs: string[], options: { reason: string }): string[] {
  return xs.map((x) => new Failure(x, options).message);
}
