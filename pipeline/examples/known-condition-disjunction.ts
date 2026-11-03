// A disjunction re-testing a Boolean constant: where `(c && x)` failed with
// `c` true, the path holds `c` at `true`, so `!c` answers `false` there and
// only that edge is built; where `c` failed, `!c` answers `true`. The next
// statement is reached where `c` is true and `x` false, as its entry claims.
// Census functions: computed-types.mts#inferredResult (its condition
// `(construct && …) || (construct && …) || (!construct && …)`).
export function plain(c: boolean, x: boolean, y: boolean, z: boolean): number {
  if ((c && x) || (c && y) || (!c && z)) return 0;
  if ((c && x) || !c) return 1;
  return c ? 2 : 3;
}

export function modifiers(
  construct: boolean,
  mods: readonly number[] | undefined,
  at: string,
): number {
  if (
    (construct && at === "result") ||
    (construct && !mods?.some((m) => m === 1)) ||
    (!construct && !!mods?.length)
  )
    return 0;
  return construct ? 1 : 2;
}
