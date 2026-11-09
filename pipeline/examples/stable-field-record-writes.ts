// A record stating one field `@stable` keeps its other fields writable: a
// compound assignment, an assignment and an update of a writable field of
// such a record write the field's location at its contract, while the stable
// field holds its object literal's value (POSITIVE-TYPES.md, "Records").

type Runs = { read: number; scripts: number; /** @stable */ readonly open: number[] };

export function make(): Runs {
  return { read: 0, scripts: 0, open: [] };
}

export function advance(runs: Runs, step: number): number {
  const { open } = runs;
  runs.read += step;
  runs.scripts &= 3;
  runs.read = runs.read + open.length;
  runs.read++;
  return runs.read;
}
