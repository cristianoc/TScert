// `Box<T>` refers to itself at `[T]`: each level of `next` applies it to a
// longer tuple, so its instances are infinitely many types, and the alias is
// one recursive head applied to them. A box of boxes is passed through.
type Box<T> = { v: T; next: Box<[T]> | null };

export function pass(b: Box<Box<number>>): Box<Box<number>> {
  return b;
}

export function first(b: Box<number>): number {
  return b.v;
}
