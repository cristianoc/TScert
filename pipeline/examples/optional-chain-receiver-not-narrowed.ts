// A chain's truthy result says its receiver is no `undefined`, which
// TypeScript reads to narrow `o` in the arm; the chain's lowering narrows the
// value it saved, and `o` stays `Outer | undefined` there.
interface Inner {
  ready: boolean;
}
interface Outer {
  inner?: Inner;
}
function use(o: Outer): number {
  return o.inner ? 1 : 0;
}
export function guarded(o: Outer | undefined): number {
  if (o?.inner) return use(o);
  return 0;
}
