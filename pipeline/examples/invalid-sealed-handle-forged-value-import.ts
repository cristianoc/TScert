// A handle forged by a cast from an object no `seal` built: a cast states no
// invariant, and is itself refused, as is the walker's call, which requires
// it. The arrays differ, and the walker reads past the view's end (run under
// Node: `forged()` reads `undefined` at `number` at `i = 1`).
import { open, type PreparedText } from "@fixture/handle";

function lastFlag(prepared: PreparedText): number {
  const internal = open(prepared);
  let last = 0;
  for (let i = 0; i < internal.widths.length; i++)
    last = internal.segmentFlags[i]!;
  return last;
}

export function forged(): number {
  const prepared = { widths: [1, 2], segmentFlags: new Uint8Array(1), label: "" } as unknown as PreparedText;
  return lastFlag(prepared);
}
