// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#materializeRichInlineLineRange.
// Refusal: gate: only field and local assignments are supported.
// A destructuring assignment to existing `let` bindings, `({ starts, ends }
// = found)`: only field and local assignments are supported.
type Sources = { starts: number[] | null; ends: number[] | null };

export function sources(flow: Sources, found: Sources): number {
  let { starts, ends } = flow;
  if (starts === null) ({ starts, ends } = found);
  return (starts?.length ?? 0) + (ends?.length ?? 0);
}
