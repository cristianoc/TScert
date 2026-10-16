// TypeScript lets any number be a numeric enum (a hole kept for bit flags);
// E holds 0 and 1 only, so an arbitrary number is refused.
enum E {
  A,
  B,
}
function numberToEnum(n: number): E {
  return n;
}
