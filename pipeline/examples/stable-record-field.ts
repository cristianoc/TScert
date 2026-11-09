// A field a record type states `@stable` holds the value its object literal
// put there for the object's life: the literal allocates the field's
// location with a contract admitting that value alone, and the type states
// the field readonly. So what is known through the field survives a call that
// may change any location, here a narrowing of `box.size` (POSITIVE-TYPES.md,
// "Records").

export type Box = {
  /** @stable */
  readonly size: number | null;
  count: number;
};

export function make(size: number | null): Box {
  return { size, count: 0 };
}

export function sizeAfter(box: Box, touch: (b: Box) => void): number {
  if (box.size === null) return 0;
  touch(box);
  return box.size;
}
