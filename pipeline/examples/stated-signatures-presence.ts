// An entry that states signatures as a value or a function, or as a list:
// the absence of both is tested by nested tests, and the printed list is
// kept where every signature has a spelling, by a filter of the spelled ones
// and a length comparison. Stands for the census function
// shadow-contracts.mts#statedSignatures and its dependent #shadowText.
type Stated = { params: string[] };
type Entry = {
  global: string;
  stated?: Stated | ((n: number) => Stated);
  forms?: Stated[];
};

const print = (s: Stated): string | null =>
  s.params.length ? s.params.join(", ") : null;

export function signatures(entry: Entry): string[] | null | undefined {
  if (entry.stated === undefined) {
    if (entry.forms === undefined) return undefined;
  }
  const n = 1;
  const stated =
    typeof entry.stated === "function" ? entry.stated(n) : entry.stated;
  const printed = [
    ...(stated === undefined ? [] : [stated]),
    ...(entry.forms ?? []),
  ].map(print);
  const spelled = printed.filter((p): p is string => p !== null);
  return spelled.length === printed.length ? spelled : null;
}
