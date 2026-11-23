// The failure of a checked read, written inline as `v ?? missing()`: a RangeError where the value is missing.
export function missing(): Modifies<{}, never> {   // PAPER: annotation
  throw new RangeError('missing value')
}
