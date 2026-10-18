// A truthy read of a readonly optional field finds the key present: the
// field's read in the branch is of the field's type.
interface Box {
  readonly kind: 2;
  readonly m?: { x: number };
}

export function inner(box: Box, f: (n: { x: number }) => number): number {
  if (box.m) return f(box.m);
  return 0;
}
