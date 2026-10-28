// The closure's parameter is a Map<string, string>, as its context says, and
// the closure passes it where a Map<string, string | number> is expected,
// which writes a number into it. Method bivariance lets TypeScript accept the
// call; `poison([new Map()])` returns 1 (run under Node), no string.
function put(m: Map<string, string | number>): void {
  m.set("k", 1);
}
export function poison(
  maps: readonly Map<string, string>[],
): string | undefined {
  maps.forEach((m) => put(m));
  const [first] = maps;
  return first?.get("k");
}
