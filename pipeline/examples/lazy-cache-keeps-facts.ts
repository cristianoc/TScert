// pretext's `getEngineProfile` (measurement.ts): a module binding caching an
// object built on first use, `cachedEngineProfile ??= buildEngineProfile()`,
// read by the line walkers between a record's facts and the reads they
// bound. `??=` writes the binding's cell only where it holds `null` or
// `undefined`, and `build` keeps the heap, so `getProfile` changes no
// location holding an object, a number or a store: it is within
// `{value: init, store: keep}` (PROGRAM-TYPING.md, "Frame conditions"). A
// call at that footprint keeps every fact over a path's objects, numbers and
// lengths: `walk` reads `prepared.segmentFlags[i]!` below
// `prepared.widths.length` after the call, and `stepped` reads at a cursor's
// field after one. `reset` writes the cell whatever it holds: its footprint
// is `{value: any, store: keep}`, and claimed at `init` it is refused at the
// write (a control in `pipeline/test.mts`).

type Profile = { epsilon: number };

let cached: Profile | null = null;

function build(): Profile {
  return { epsilon: 0.005 };
}

export function getProfile(): Profile {
  return cached ??= build();
}

export function reset(): void {
  cached = null;
}

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: number[] };

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

export function walk(prepared: Prepared, maxWidth: number): number {
  let count = 0;
  for (let i = 0; i < prepared.widths.length; i++) {
    const limit = maxWidth + getProfile().epsilon;
    if (prepared.widths[i]! > limit && prepared.segmentFlags[i]! !== 0) count++;
  }
  return count;
}

/** @requires safeInteger(cursor.segmentIndex) && cursor.segmentIndex < prepared.widths.length */
export function stepped(prepared: Prepared, cursor: Cursor): number {
  const epsilon = getProfile().epsilon;
  return prepared.segmentFlags[cursor.segmentIndex]! + epsilon;
}
