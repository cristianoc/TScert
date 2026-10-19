// A declaration's members keyed by well-known symbols other than the tag
// are read as declared: an iterable's `[Symbol.iterator]` and a declared
// class's `[Symbol.toStringTag]` field, an own field no prototype holds.
declare class Bag {
  readonly [Symbol.toStringTag]: string;
  [Symbol.iterator](): Iterator<number>;
}

export function label(b: Bag): string {
  return b[Symbol.toStringTag];
}

export function count(xs: Iterable<number>): number {
  let n = 0;
  for (const _ of xs) n++;
  return n;
}
