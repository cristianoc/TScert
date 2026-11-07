// A `WeakMap`'s `set` and `delete` write only the table, host state no
// location of the model holds, and state the empty footprint, so a call of
// either keeps every heap fact (`call-keep`): a path's length bound a
// precondition states survives a cache filled on a miss (`withMap`, pretext's
// `getSegmentMetrics` caches) and a deletion (`dropped`) (SOURCE-CONTRACTS.md,
// "Weak tables").

type P = { segments: string[] };
const caches = new WeakMap<P, Map<number, number>>();

/** @requires safeInteger(i) && 0 <= i && i < p.segments.length */
export function withMap(p: P, i: number): string {
  let cache = caches.get(p);
  if (cache === undefined) {
    cache = new Map<number, number>();
    caches.set(p, cache);
  }
  return p.segments[i]!;
}

/** @requires safeInteger(i) && 0 <= i && i < p.segments.length */
export function dropped(p: P, i: number): string {
  caches.delete(p);
  return p.segments[i]!;
}
