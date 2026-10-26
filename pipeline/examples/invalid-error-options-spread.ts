// A copy of a value whose type does not state `cause` holds whatever own
// enumerable `cause` it had, its getter's result where it had a getter,
// which the copy runs: the copy's type does not state `cause` either.
// Refused at the options.
export function wrong(xs: string[], extra: { reason: string }): string[] {
  return xs.map((x) => Error(x, { ...extra }).message);
}
