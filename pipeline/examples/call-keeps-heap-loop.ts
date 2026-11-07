// A call of a function whose loop writes only its own locals keeps the
// heap: a write of a local held in a slot changes no location, so `count`'s
// signature states the empty footprint, and the bound `i < b.length` on the
// typed array survives the call (`call-keep`).

function count(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) s = s + 1;
  return s;
}

export function weighted(b: Uint8Array, xs: number[]): number {
  let s = 0;
  for (let i = 0; i < b.length; i++) {
    if (count(xs) > 0) s = s + 1;
    s = s + b[i]!;
  }
  return s;
}
