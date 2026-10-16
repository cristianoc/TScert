// A member initializer reading a later member, here through a closure it
// calls at once, which TypeScript accepts: the member is not yet written, so
// the read gives undefined, and `F.A`, typed `number`, holds undefined. A read
// of a member not yet initialized is refused.
enum F {
  A = ((): number => F.B)(),
  B = 1,
}
function first(): number {
  const f = F;
  return f.A;
}
