// A chain's truthy result in a condition says its receiver is no
// `undefined`: `o?.inner` there is `o != null && o.inner`, which narrows `o`
// in the arm.
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
