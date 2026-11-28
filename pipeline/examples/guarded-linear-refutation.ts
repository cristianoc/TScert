// Linear refutation of a guarded fact's body (`guarded s p g B` where held
// linear facts refute `B`) discharges guard tag `g` on `s.p`, refining slot
// types and discharging complementary guards.
type Holder = { field: { value: number } | null };

/** @requires safeInteger(x)
 *  @requires obj.field !== null || x >= 0
 */
export function readWhenNegative(x: number, obj: Holder): number {
  if (x < 0) {
    return obj.field!.value;
  }
  return x;
}

type Items = { halts: Float64Array | null };
type Data = { widths: number[]; items?: Items };

/** @invariant safeInteger(this.onlyItem)
 *  @invariant this.data.items !== undefined || this.onlyItem >= 0
 *  @invariant this.data.items === undefined || this.data.items.halts === null || this.data.widths.length <= this.data.items.halts.length
 *  @invariant this.segmentItems !== null || this.onlyItem >= 0
 *  @invariant this.segmentItems === null || this.segmentItems.length === this.data.widths.length
 */
type Flow = {
  data: Data;
  onlyItem: number;
  segmentItems: Int32Array | null;
};

/** @requires safeInteger(flow.onlyItem) && flow.onlyItem < 0
 *  @requires safeInteger(i) && 0 <= i && i < flow.data.widths.length
 */
export function readFlow(flow: Flow, i: number): number {
  const data = flow.data;
  const items = data.items;
  const rawSegs = flow.segmentItems;
  const segs: Int32Array = rawSegs!;
  const halts = items!.halts;
  const h = halts !== null ? halts[i]! : 0;
  return segs[i]! + h;
}
