// Method calls preserve the facts their signatures' footprints preserve: a
// `WeakMap`'s `get` and a `Map`'s construction state the empty footprint,
// whose calls preserve every heap fact (`call-keep`), so a path's length bound a
// precondition states is preserved by the lookup (`cached`); a `Map`'s `set` states
// `{value: any, store: keep}`, which keeps every store, so a length bound
// survives it (`mapped`) (SOURCE-CONTRACTS.md, "Weak tables").

type Prepared = { segments: string[] };
const caches = new WeakMap<Prepared, number>();

/** @requires safeInteger(i) && 0 <= i && i < p.segments.length */
export function cached(p: Prepared, i: number): string {
  const hit = caches.get(p);
  if (hit === undefined) return "";
  return p.segments[i]!;
}

export function mapped(xs: number[]): number {
  const m = new Map<number, number>();
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    m.set(i, i);
    s = s + xs[i]!;
  }
  return s;
}
