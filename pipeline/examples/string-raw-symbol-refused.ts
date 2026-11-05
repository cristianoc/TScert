// A symbol substitution of `String.raw`: its ToString throws a TypeError,
// which a string's concatenation has no rule for, so it is refused, as in a
// template literal.
export function described(s: symbol): string {
  return String.raw`${s}`;
}
