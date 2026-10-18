// `Object.values` is admitted only as a call: passed as a value, its
// parameter's obligation would not be checked (COMPILER-API.md, "First-class
// library values").
function consume(f: unknown): number {
  return 0;
}
export function f(): number {
  return consume(Object.values);
}
