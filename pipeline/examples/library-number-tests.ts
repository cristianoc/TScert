// `Number` and `Object` members through the reviewed overlay:
// `Number.isFinite`, `Number.isInteger` and `Number.isSafeInteger` of any
// value, which convert nothing, and `Object.is` of any two values.
function finite(x: unknown): boolean {
  return Number.isFinite(x) && Number.isInteger(x) && Number.isSafeInteger(x);
}

function same(a: { k: number }, b: unknown): boolean {
  return Object.is(a, b) || Object.is(0 / 0, 0 / 0);
}
