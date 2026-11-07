// A sealed handle whose `@representation` names an intersection of record
// types, pretext's `PreparedLineData = PreparedLineBreakData & { items?:
// ParagraphSegmentData }`: a value of it has the fields of both parts, so the
// invariant's paths read `PreparedLineBreakData`'s fields. The builder's cast
// of a literal without `items` meets the representation, and each function
// taking the handle assumes `segmentFlags.length === widths.length`.

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
};

type ParagraphSegmentData = { texts: string[] };

type PreparedLineData = PreparedLineBreakData & {
  items?: ParagraphSegmentData;
};

type InternalPreparedText = PreparedText & PreparedLineData;

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length);
  return {
    widths,
    segmentFlags,
  } satisfies PreparedLineData as unknown as PreparedText;
}

function getInternalPrepared(prepared: PreparedText): InternalPreparedText {
  return prepared as InternalPreparedText;
}

export function countBreaks(prepared: PreparedText): number {
  const internal = getInternalPrepared(prepared);
  let n = 0;
  for (let i = 0; i < internal.widths.length; i++) {
    if (internal.segmentFlags[i]! === 1) n++;
  }
  return n;
}

export function itemCount(prepared: PreparedText): number {
  const internal = getInternalPrepared(prepared);
  return internal.items === undefined ? 0 : internal.items.texts.length;
}
