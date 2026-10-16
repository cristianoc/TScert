// Each shape's `toString` takes its own receiver: the call through the union
// of the two members is dispatched by shape, the member read and called with
// the value as its receiver in one step, after the actuals.
function unionToString(x: string | number): string {
  return x.toString();
}
function unionAt(x: string | number | boolean): string {
  return x.toString();
}
