// Method signatures in type literals are host-relative members, as an
// interface's are: read off their object and invoked on it. In an alias's own
// body, nested in a declaration, and in an annotation.
type Counter = { count: number; bump(): number; reset?(): void };
type Holder = { inner: { get(): string } };
type Pair = [{ at(i: number): string }];
declare const counter: Counter;
declare const holder: Holder;
declare const pair: Pair;
function call(o: { m(x: number): number; n: number }): number {
  return o.m(o.n);
}
function nested(o: { inner: { get(): string } }): string {
  return o.inner.get();
}
export function use(): number {
  return (
    counter.bump() +
    holder.inner.get().length +
    pair[0].at(0).length +
    nested(holder).length
  );
}
export function forward(o: { m(x: number): number; n: number }): number {
  return call(o);
}
