// A sealed handle (PROGRAM-TYPING.md, "Type invariants"), pretext's
// `PreparedText`: a branded type with no field of its own, which means its
// representation (`@representation PreparedLineBreakData`), with an invariant
// over the representation's fields. The builder casts a literal into the
// handle (`satisfies … as unknown as PreparedText`), the obligation that the
// literal is a `PreparedLineBreakData`, and its return proves the invariant;
// `getInternalPrepared` casts out, which the meaning gives. Each function
// taking the handle assumes `segmentFlags.length === widths.length`, so
// `countBreaks` reads `segmentFlags[i]!` below `widths.length`. A write of
// the field `label`, which the invariant does not read, keeps it; so do a
// parameter's default and a literal's allocation. A result of a union each
// of whose arms names the handle states its invariant.

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineBreakData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
  label: string;
};

type InternalPreparedText = PreparedText & PreparedLineBreakData;

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length);
  for (let i = 0; i < widths.length; i++)
    segmentFlags[i] = widths[i]! === 0 ? 1 : 0;
  return { widths, segmentFlags, label: "" } satisfies PreparedLineBreakData as unknown as PreparedText;
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

export function labelled(prepared: PreparedText): number {
  const internal = getInternalPrepared(prepared);
  internal.label = "counted";
  return countBreaks(internal);
}

// A parameter with a default beside the handle, and a literal allocated
// before the handle is passed on: neither changes a location the invariant
// reads.
export function counted(prepared: PreparedText, from: number = 0): number {
  const stats = { lines: from };
  return countBreaks(prepared) + stats.lines;
}

// A result of a union each of whose arms names the handle: the handle's
// invariant is a fact of the result, which each return establishes.
function reopened(prepared: PreparedText, again: boolean):
    (PreparedText & PreparedLineBreakData) | (PreparedText & { readonly label: string }) {
  return again ? getInternalPrepared(getInternalPrepared(prepared)) : getInternalPrepared(prepared);
}

export function layout(texts: string[]): number {
  return labelled(reopened(prepare(texts), texts.length > 1)) + counted(prepare(texts));
}
