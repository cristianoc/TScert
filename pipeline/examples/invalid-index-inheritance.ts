type Scores = { readonly [name: string]: number };

interface Match extends Scores {
  readonly home: number;
}

// A record with the named member but without the inherited index is not a
// Match: its other keys are unconstrained.
export function promote(r: { readonly home: number }): Match {
  return r;
}
