// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#findWholeLine.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim.
// A closure taking fewer parameters than the visitor an imported function's
// optional parameter states: no claim of the call meets the imported
// signature. The same closure declaring every parameter verifies.
import { walkLines, type LineData } from "../pretext-project/line-data.ts";

export function widest(data: LineData): number {
  let max = 0;
  walkLines(data, 100, (width) => {
    if (width > max) max = width;
  });
  return max;
}
