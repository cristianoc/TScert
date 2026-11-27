// Positive case: by ECMA-262 TypedArrayGetElement (`%ByteAt%`), a typed-array
// element read that yields a value other than `undefined` read a valid integer
// index `0 <= k < view.length`, establishing integrality and bounds on `k`.

export function writeOnDefinedUint8(
  bytes: Uint8Array,
  out: Dense<number[]>,
  k: number,
): number {
  if (out.length !== bytes.length) return -1;
  const b = bytes[k];
  if (b === undefined) throw new RangeError("index");
  out[k] = b + 1;
  return out[k]!;
}

export function readOnCoalescedInt32(
  xs: Int32Array,
  ys: number[],
  k: number,
): number {
  if (ys.length !== xs.length) return 0;
  const v =
    xs[k] ??
    (() => {
      throw new RangeError("index");
    })();
  return v + ys[k]!;
}

export function readOnDefinedFloat64(
  xs: Float64Array,
  ys: number[],
  k: number,
): number {
  if (ys.length < xs.length) return 0;
  const v = xs[k];
  if (v === undefined) return 0;
  return v + ys[k]!;
}
