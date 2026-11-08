// pretext's `getGraphemeEnds` (line-text.ts): per handle, a `Map` from a
// segment's index to its grapheme ends, kept in a `WeakMap` and filled on
// first use. A `Map`'s `set` writes its table, which no location of the
// model holds, and its `size`, a number: within `{value: scalar, store:
// keep}`, which alters no location holding an object or a store
// (SOURCE-CONTRACTS.md, "Native footprints"). So `ends` is within it too,
// and `buildText`, pretext's `buildRangeText`, reads
// `prepared.segments[i]!` below `prepared.segments.length` after each call:
// the path's object and the store's length are kept. A fact over a number
// field is not: the `size` the call sets could be any number's location.

export type Prepared = { widths: number[]; segments: string[] };

const caches = new WeakMap<string[], Map<number, number>>();

/** @requires safeInteger(i) && 0 <= i && i < segments.length */
export function ends(segments: string[], i: number): number {
  let cache = caches.get(segments);
  if (cache === undefined) {
    cache = new Map<number, number>();
    caches.set(segments, cache);
  }
  let end = cache.get(i);
  if (end === undefined) {
    end = segments[i]!.length;
    cache.set(i, end);
  }
  return end;
}

export function buildText(prepared: Prepared): string {
  let text = "";
  for (let i = 0; i < prepared.segments.length; i++) {
    const end = ends(prepared.segments, i);
    text += prepared.segments[i]!.slice(end);
  }
  return text;
}
