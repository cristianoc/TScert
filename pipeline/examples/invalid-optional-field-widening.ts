// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// layout.ts#layout, layout.ts#layoutWithLines, layout.ts#measureLineStats,
// layout.ts#stepNextLine, layout.ts#walkLineRanges.
// Refusal: reject: source expression obligation.
// A record passed where its type plus an optional field is expected:
// TypeScript admits it, but a value of the narrower type may hold that
// field at another type: under Node, `layout({ widths: [1, 2], items: 5 })`
// returns undefined where a number is due, and no claim meets the parameter.
// Pretext's handle comes only from prepare(), which builds it without
// `items`; pretext states it in the handle's type (`items?: never`) and
// the walkers' (`readonly items?`), a rewrite of TScert issue #94.
type Data = { widths: number[] };
type LineData = Data & { items?: { count: number } };

function countLines(prepared: LineData): number {
  return prepared.items === undefined
    ? prepared.widths.length
    : prepared.items.count;
}

export function layout(prepared: Data): number {
  return countLines(prepared);
}
