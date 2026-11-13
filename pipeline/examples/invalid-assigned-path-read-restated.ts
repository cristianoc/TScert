// The path's postcondition one short (`breaks.length === source.length`):
// the restated fact gives `breaks.length = s.length`, and the read at
// `s.length` is refused (run under Node: `last("ab")` reads index 2 of a
// two-element array, `undefined` at `number`, and returns `NaN`).
export type Scan = { breaks: Uint8Array; leftOut: Uint8Array | null };

/** @ensures result.breaks.length === source.length */
export function scan(source: string): Scan {
  const flags = new Uint8Array(source.length);
  return { breaks: flags, leftOut: null };
}

export function last(source: string): number {
  let breaks: Uint8Array;
  const g = scan(source);
  breaks = g.breaks;
  let count = 0;
  for (let i = 0; i < source.length; i++) if (source.charCodeAt(i) !== 32) count++;
  return breaks[source.length]! + count;
}
