// A call keeping the heap between a guard and the field's reread keeps what
// the guard found: `count` changes no location the call starts with.
function isList(value: readonly number[] | number): value is readonly number[] {
  return Array.isArray(value);
}
function count(value: readonly number[]): number {
  return value.length;
}
export function size(x: { args: readonly number[] | number }): number {
  if (isList(x.args)) {
    const n = count(x.args);
    return n + x.args.length;
  }
  return 0;
}
