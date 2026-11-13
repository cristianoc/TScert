// A write at a checked index into an array a record's field holds, after
// `out.xs ??= …`: what is known of the field's contents (not null) holds of
// the written value and of an array store too, so the write keeps it
// whatever it aliases (`weak-update`, `IndexWrites.writtenCells`), and the
// closure's exit, where the field is narrowed, is reached (pretext's
// `getHanKerningTrims`, its `addWidthTrim`).
export type Trims = { xs: number[] | null };

export function trims(n: number): Trims {
  const out: Trims = { xs: null };
  const add = (i: number, v: number): void => {
    out.xs ??= [0, 0, 0];
    const store = out.xs;
    if ((i & 0x7fffffff) !== i || i > store.length) throw new RangeError("index");
    store[i] = v;
  };
  if (Number.isSafeInteger(n) && n >= 0 && n < 3) add(n, 1);
  return out;
}

