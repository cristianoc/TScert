// A field stated `@stable` is met only by an object whose field's location
// admits one value: an object literal allocated at that type. An object with
// a writable `size`, which TypeScript lets stand for the readonly field, is
// no `Box`, and the narrowing it would have kept across `touch` is refused.
// Under Node, `run()` gets `null` from `sizeAfter` at `number`.

export type Box = {
  /** @stable */
  readonly size: number | null;
  count: number;
};

export function sizeAfter(box: Box, touch: (b: Box) => void): number {
  if (box.size === null) return 0;
  touch(box);
  return box.size;
}

export function run(): number | null {
  const open: { size: number | null; count: number } = { size: 1, count: 0 };
  return sizeAfter(open, () => { open.size = null; });
}
