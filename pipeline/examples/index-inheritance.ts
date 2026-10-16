// An interface extending an index signature type has its own named members
// and the inherited index, which constrains the named members too.
type Scores = { readonly [name: string]: number };

interface Match extends Scores {
  readonly home: number;
  readonly away: number;
}

export function home(m: Match): number {
  return m.home;
}

export function other(m: Match): number | undefined {
  return m["extra"];
}

export function scores(m: Match): Scores {
  return m;
}

// A fresh literal is one: its own keys are exactly the named members, each
// within the index.
export function fresh(): Match {
  return { home: 1, away: 2 };
}
