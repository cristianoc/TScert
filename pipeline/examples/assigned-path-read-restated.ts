// A `let` assigned a field path's read (`breaks = scan(s).breaks`): the
// loop heads after it are proposed the facts of the path restated over the
// binding, as a declaration's are (`Ctx.bindTo`): the postcondition's
// `breaks.length = s.length + 1` reaches the reads at `s.length` past the
// loops (pretext's `analyzeText`, its Gecko branch).
export function missing(): never {
  throw new RangeError("missing value");
}

export type Scan = { breaks: Uint8Array; leftOut: Uint8Array | null };

/** @ensures result.breaks.length === source.length + 1 */
export function scan(source: string): Scan {
  const flags = new Uint8Array(source.length + 1);
  return { breaks: flags, leftOut: null };
}

export function atomicLoop(source: string, atomic: boolean[] | null, starts: number[]): number {
  let breaks: Uint8Array;
  const g = scan(source);
  breaks = g.breaks;
  if (atomic !== null) {
    for (let k = 0; k < atomic.length; k++) {
      if (!atomic[k]) continue;
      let after = (starts[k] ?? missing()) + 1;
      while (after < source.length && source.charCodeAt(after) === 32) after++;
      breaks[after] = (breaks[after] ?? missing()) & 3;
    }
  }
  return breaks[source.length]!;
}

export function copyLoop(source: string): number {
  let breaks: Uint8Array;
  const g = scan(source);
  breaks = g.breaks;
  let count = 0;
  for (let i = 0; i < source.length; i++) {
    if (source.charCodeAt(i) === 32) continue;
    breaks[count++] = breaks[i]!;
  }
  breaks[count] = breaks[source.length]!;
  return count;
}
