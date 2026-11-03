// A map callback whose only call of unrestricted effect makes the error it
// throws: that call and the throw have no normal exit, so the callback's
// normal-return footprint leaves them out and the mapped array is readable.
// Census functions: declaration-graph.mts#importBindings.
export function lengths(
  xs: readonly (string | null)[],
  fail: (at: number) => Error,
): readonly number[] {
  return xs.map((x, at) => {
    if (x === null) throw fail(at);
    return x.length;
  });
}
