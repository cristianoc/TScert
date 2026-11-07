// A sealed handle's invariant (PROGRAM-TYPING.md, "Record invariants"),
// pretext's `PreparedText`: `@fixture/handle` declares the branded handle,
// its representation `PreparedLineBreakData` and its invariant over the
// representation's fields (`@representation`), and `seal` and `open`, its
// casts in and out. Each function taking the handle assumes
// `segmentFlags.length === widths.length` of it; `open` states it of the
// record it returns, so `countBreaks` reads `segmentFlags[i]!` below
// `widths.length`. The builder establishes the representation's invariant at
// its call of `seal`; a write of the field `label` of the opened record,
// which the invariant does not read, keeps it, and the record, a handle too
// (`PreparedText & PreparedLineBreakData`), is passed on; so are a parameter's
// default and a literal's allocation. A result of a union each of whose arms
// names the handle states its invariant.
import { open, seal, type PreparedLineBreakData, type PreparedText } from "@fixture/handle";

export function prepare(texts: string[]): PreparedText {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  const segmentFlags = new Uint8Array(widths.length);
  for (let i = 0; i < widths.length; i++)
    segmentFlags[i] = widths[i]! === 0 ? 1 : 0;
  return seal({ widths, segmentFlags, label: "" });
}

export function countBreaks(prepared: PreparedText): number {
  const internal = open(prepared);
  let n = 0;
  for (let i = 0; i < internal.widths.length; i++) {
    if (internal.segmentFlags[i]! === 1) n++;
  }
  return n;
}

export function labelled(prepared: PreparedText): number {
  const internal = open(prepared);
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
  return again ? open(open(prepared)) : open(prepared);
}

export function layout(texts: string[]): number {
  return labelled(reopened(prepare(texts), texts.length > 1)) + counted(prepare(texts));
}
