// Booleans compared relationally convert to numbers first: `false` to 0 and
// `true` to 1, which runs no code.
function order(a: boolean, b: boolean): boolean {
  return a < b;
}
function atMostTrue(a: boolean): boolean {
  return a <= true;
}
