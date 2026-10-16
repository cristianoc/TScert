type Scores = { readonly [name: string]: number };

interface Match extends Scores {
  readonly home: number;
}

// Only the named member is known present; any other key may be missing.
export function away(m: Match): number {
  return m["away"];
}
