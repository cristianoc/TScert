// A call stated `Fresh<number[]>` returns a spine apart from every existing
// array, including field-rooted arrays across a loop.
function zeros(count: number): Modifies<{}, Fresh<number[]>> {
  const out: number[] = [];
  for (let i = 0; i < count; i++) out.push(0);
  return out;
}

export type PairData = {
  readonly flags: Uint8Array;
  readonly widths: number[];
};

/**
 * @requires data.flags.length === data.widths.length
 */
export function fillAndRead(data: PairData, count: number): number {
  let spaces = zeros(count);
  let total = 0;
  /** @invariant data.flags.length === data.widths.length && spaces !== data.widths */
  for (let i = 0; i < data.flags.length; i++) {
    if (i < count) {
      if ((i & 0x7fffffff) !== i || i > spaces.length)
        throw new RangeError("index");
      spaces[i] = data.flags[i]!;
    }
    total += data.widths[i]!;
    if (i === 0) spaces = zeros(count);
  }
  return total;
}
