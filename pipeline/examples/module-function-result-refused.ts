// A module function without a result annotation: its slot is its annotated
// signature, at which its unit is checked and every call reads it, and this
// declaration writes none. TypeScript infers `number`.
function next(x: number) {
  return x + 1;
}
export function two(): number {
  return next(1);
}
