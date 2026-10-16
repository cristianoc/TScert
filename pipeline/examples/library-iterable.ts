// The standard library's Iterable, read from its declarations: it reaches
// Iterator, whose `next` takes `...[value]: [] | [TNext]` and whose `return?`
// and `throw?` are optional methods.
export function same(x: Iterable<number>): Iterable<number> {
  return x;
}
