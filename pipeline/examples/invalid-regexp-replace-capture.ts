// Group 1 sits under an alternative: on "b" the callback is handed
// `undefined` for it, so a callback taking it as a string is refused.
export function last(s: string): string {
  let seen = "";
  s.replace(/(a)|(b)/g, (_: string, a: string) => {
    seen = a;
    return "";
  });
  return seen;
}
