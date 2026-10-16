// A member initializer calling a module function that reads the enum, which
// TypeScript accepts: the enum's object is not complete while the initializer
// runs, so `H.B` reads undefined, and `H.A`, typed `number`, holds undefined.
// The initialization order check refuses a call that can read a constant not
// yet initialized.
function second(): number {
  return H.B;
}
enum H {
  A = second(),
  B = 1,
}
function first(): number {
  const h = H;
  return h.A;
}
