// `Box<T>` holds a writable `T`, so it is invariant: a `Box<number>` is no
// `Box<number | null>`, through which `null` could be written where the
// original promises a number (TypeScript relates the field covariantly).
type Box<T> = { v: T; next: Box<[T]> | null };

export function widen(b: Box<number>): Box<number | null> {
  return b;
}

export function wrong(b: Box<number>): number {
  widen(b).v = null;
  return b.v;
}
