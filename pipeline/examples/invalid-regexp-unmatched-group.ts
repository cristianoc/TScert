// `/(a)|b/` leaves group 1 unmatched on "b": it is no string.
export function first(s: string): string {
  const m = /(a)|b/.exec(s);
  return m ? m[1] : "";
}
