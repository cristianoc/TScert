// The step-frame rule (FOOTPRINTS.md, "Argument-path store regions"): each
// step's frame, read at its own positions, is rebased to the enclosing
// entry through the slot it reads and included in the stated frame.
// `note`'s `push` changes the store of the array `runs.open` reads (the
// narrower frame `ReceiverGrows` states, every other old location kept);
// `scan` changes it only by calling `note` with its own `runs`, whose
// frame rebases to `scan`'s region through the stable field. `measure`
// allocates the record, so its literal's array is apart from `flags`, and
// keeps `i < flags.length` across each call of `scan`.
type Runs = { /** @stable */ readonly open: number[] };

function note(runs: Runs, c: number): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  runs.open.push(c, 0);
}

function scan(runs: Runs, text: string): Modifies<{ values: "any"; "runs.open[*]": "any" }, void> {
  for (let i = 0; i < text.length; i++) note(runs, text.charCodeAt(i));
}

export function measure(flags: number[]): number {
  const runs: Runs = { open: [] };
  let sum = 0;
  for (let i = 0; i < flags.length; i++) {
    scan(runs, "x");
    sum += flags[i]!;
  }
  return sum;
}
