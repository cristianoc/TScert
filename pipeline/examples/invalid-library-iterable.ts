// An Iterable is not an Iterator: its `next` is not a member.
export function wrong(x: Iterable<number>): Iterator<number> {
  return x;
}
