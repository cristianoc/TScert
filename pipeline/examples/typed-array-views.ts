// The standard library's `Uint8Array`, `Uint16Array` and `Int32Array`, as
// pretext uses them (chenglou/pretext at 0d102a5c, src/): record fields and
// parameters, construction at a length and from an array of numbers,
// element reads and writes at a number, `length`, and the methods `fill`,
// `copyWithin`, `set` and `subarray`.
export type Runs = {
  index: Uint16Array;
  values: Uint8Array;
  ends: Int32Array | null;
};

export function unpack(blocks: number): Runs {
  const index = new Uint16Array(0x100);
  const values = new Uint8Array(blocks << 8);
  const whole = new Int32Array(0x100).fill(-1);
  for (let i = 0; i < index.length; i++) index[i] = i;
  values.fill(1, 0, 8);
  values.copyWithin(8, 0, 8);
  index.set(new Uint16Array([1, 2, 3]), 1);
  return { index, values, ends: whole.subarray(0, 4) };
}

export function mark(len: number, at: number): Uint8Array | null {
  let leftOut: Uint8Array | null = null;
  if (at < len) (leftOut ??= new Uint8Array(len))[at] = 1;
  return leftOut;
}

export function first(runs: Runs): number {
  const ends = runs.ends;
  const end = ends === null ? undefined : ends[0];
  return (runs.values[0] ?? 0) + (runs.index[1] ?? 0) + (end ?? 0);
}
