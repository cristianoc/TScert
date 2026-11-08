// `getProfile` caches its object with `??=`, but its initializer first pops
// the record's flags: the call changes a store, so it is no initialization
// of the cell alone, and the walker's read at the last index after the call
// is refused. Run under Node, the read gives `undefined`.

type Profile = { epsilon: number };

let cached: Profile | null = null;

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: number[] };

function build(flags: number[]): Profile {
  flags.pop();
  return { epsilon: 0.005 };
}

export function getProfile(flags: number[]): Profile {
  return cached ??= build(flags);
}

/** @requires 0 < prepared.widths.length */
export function last(prepared: Prepared): number {
  if (getProfile(prepared.segmentFlags).epsilon < 0) return 0;
  return prepared.segmentFlags[prepared.widths.length - 1]!;
}
