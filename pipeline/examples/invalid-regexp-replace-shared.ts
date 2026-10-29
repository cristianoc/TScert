// A regex held in a binding may reach other code, which can give it a
// `lastIndex` whose `valueOf` compiles another pattern before the match: the
// callback's arguments then follow no shape, so only a literal written at
// the call takes a replacement callback.
export function first(s: string, share: (r: object) => void): string {
  const r = /(a)/;
  share(r);
  let seen = "";
  s.replace(r, (_: string, a: string) => {
    seen = a;
    return "";
  });
  return seen;
}
