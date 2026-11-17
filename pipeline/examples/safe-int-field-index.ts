// A field typed `SafeInt` read through a path bounding an index: the
// precondition names `b.count` with no `safeInteger`, its type stating it
// a safe integer, and the caller establishes it by a test of the field.

type Buffer = { readonly items: number[]; readonly count: SafeInt };

/** @requires 0 <= b.count && b.count < b.items.length */
function at(b: Buffer): number {
  return b.items[b.count]!;
}

export function current(b: Buffer): number {
  if (0 <= b.count && b.count < b.items.length) return at(b);
  return 0;
}
