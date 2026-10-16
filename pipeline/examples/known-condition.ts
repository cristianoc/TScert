// A condition whose type is a Boolean literal takes one arm, and only that arm
// needs the result's type (`ifKnown`): `ready` is `true`, so `ready || zs[0]`
// is `true`, and the element read, which may find a hole, never runs.
export function known(ys: true[]): true | undefined {
  const ready = true;
  const pick = (zs: true[]): true | undefined => ready || zs[0];
  return pick(ys);
}

// The second test is skipped once the loop's first test is false.
export function guardedLoopRead(x: string | null, again: boolean): void {
  while (x !== null && again) {
    const text: string = x;
    x = null;
  }
}
