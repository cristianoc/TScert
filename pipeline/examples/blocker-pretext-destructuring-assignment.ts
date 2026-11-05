// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#materializeRichInlineLineRange.
// A destructuring assignment to existing `let` bindings, `({ starts, ends }
// = found)`: the right side once, then each property read and written to
// its target in turn.
type Sources = { starts: number[] | null; ends: number[] | null };

export function sources(flow: Sources, found: Sources): number {
  let { starts, ends } = flow;
  if (starts === null) ({ starts, ends } = found);
  return (starts?.length ?? 0) + (ends?.length ?? 0);
}
