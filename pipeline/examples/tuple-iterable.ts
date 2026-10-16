// A tuple is an `Iterable` of the union of its positions: expected at an
// iterable other than an array, it is read as the readonly array of its
// positions, whose prototype's `[Symbol.iterator]` yields them.
export function homogeneous(): Iterable<number> {
  const t: [number, number] = [1, 2];
  const it: Iterable<number> = t;
  return it;
}

export function heterogeneous(
  t: [number, string, boolean],
): Iterable<number | string | boolean> {
  return t;
}

function takesIterable<T>(x: Iterable<T>): void {
  void x;
}

export function generic(): void {
  const t: [number, string] = [1, "a"];
  takesIterable<number | string>(t);
}
