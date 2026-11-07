// A function resizing one array of a handle it opened, then passing the
// handle on: the `push` changes `widths.length`, so the handle's invariant
// the walker's call requires no longer holds, and the call is refused. The
// walker then reads past the view's end (run under Node: `grown` of a handle
// of one segment reads `undefined` at `number` at `i = 1`).
import { open, type PreparedText } from "@fixture/handle";

function lastFlag(prepared: PreparedText): number {
  const internal = open(prepared);
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function grown(prepared: PreparedText): number {
  open(prepared).widths.push(0);
  return lastFlag(prepared);
}
