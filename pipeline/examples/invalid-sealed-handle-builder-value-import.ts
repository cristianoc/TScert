// A builder sealing arrays of different lengths: the call of `seal`, which
// requires the representation's invariant `segmentFlags.length ===
// widths.length`, is refused. The walker then reads past the view's end (run
// under Node: `layout(["a", "b"])` reads `undefined` at `number` at `i = 1`).
import { open, seal, type PreparedText } from "@fixture/handle";

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return seal({ widths, segmentFlags: new Uint8Array(1), label: "" });
}

function lastFlag(prepared: PreparedText): number {
  const internal = open(prepared);
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function layout(texts: string[]): number {
  return lastFlag(prepare(texts));
}
