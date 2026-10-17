// A callback scanning back over trailing spaces through an optional chain,
// as `record-render.mts`'s `mathRoles` does: the chain reads, so the callback
// is within `{value: any, store: keep}` and the result is dense.
type Token = { kind: string; text: string };
export function lastWords(lines: Token[][]): number[] {
  return lines.map((ts: Token[]): number => {
    let j = ts.length - 1;
    while (ts[j]?.kind === "space") j--;
    return j;
  });
}
