// `.call` of a method read off its object passes it a receiver other than
// that object, where a method's contract is relative to it: TypeScript
// admits any receiver there (`o.value.call({}, 1)` too), which is unsound.
class Counter {
  count: number = 1;
  value(a: number): number {
    return this.count + a;
  }
}
export function other(o: Counter, p: Counter): number {
  return o.value.call(p, 1);
}
