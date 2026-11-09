// Census functions: fragment-statements.mts#statements.
// An array literal spreading a value that is one of two arrays, a readonly
// parameter or a fresh copy of part of it: the literal reads the store of
// whichever it holds, which changes no location, so the function meets the
// footprint it states.
export function scope(
  list: readonly string[],
  end: number,
): Modifies<{ values: "any"; stores: "grow" }, string[]> {
  const live = end < 0 ? list : list.slice(0, end + 1);
  const tail = list.slice(live.length).filter((s) => s.startsWith("function"));
  return [...live, ...tail];
}
