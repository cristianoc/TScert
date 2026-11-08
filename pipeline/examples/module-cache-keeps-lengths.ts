// pretext measurement.ts: addMetrics counts each measurement in a module
// cache's field (`measurement.state.segments++`) and reads a module `let`
// binding. Reading a module binding changes no location, and a field
// update writes one location holding a number, so the function keeps every
// store (`{value: any, store: keep}`) and a caller's loop keeps the length
// its reads are bounded by.

type State = { segments: number };
let state: State | null = null;

function count(): number {
  if (state === null) state = { segments: 0 };
  const s: State = state;
  s.segments++;
  return s.segments;
}

export function total(xs: number[]): number {
  let t = 0;
  for (let i = 0; i < xs.length; i++) t += count() + xs[i]!;
  return t;
}
