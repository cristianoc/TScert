// The fact gives the array no type: returned at readonly string[] after the
// test, a later push of null through the caller's alias would break that
// type, as Node shows at the last line.
export function view(xs: (string | null)[]): readonly string[] {
  return xs.every((x): x is string => x !== null) ? xs : [];
}
