// A symbol-keyed field is a key of its own: a branded value passes at its
// declared type, and its string-keyed field reads as usual.
import { unwrap, wrap, type Branded } from "@fixture/lib";
export function roundTrip(n: number): number {
  const b: Branded = wrap(n);
  return unwrap(b) + b.n;
}
