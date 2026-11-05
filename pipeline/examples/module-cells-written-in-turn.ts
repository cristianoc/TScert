// Two module cells written in turn, then a call run with them set aside:
// two module cells are two locations, so after the second write both
// cells' contents are known.
// Census functions: declaration-session.mts#asideForTests.
type Session = { readonly name: string; readonly uses: Map<string, number> };

let retaining: boolean = false;
let retained: Session | null = null;

export function aside<T>(run: () => T): T {
  const held = retained,
    was = retaining;
  retained = null;
  retaining = false;
  try {
    return run();
  } finally {
    retained = held;
    retaining = was;
  }
}
