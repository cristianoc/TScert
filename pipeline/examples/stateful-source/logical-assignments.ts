/**
 * Logical assignment to a field or an element: the target's parts are
 * evaluated once, its value read, and the right side written only when the
 * test on that value says so. `??=` tests for null or undefined; `||=` and
 * `&&=` need a Boolean target, since truthiness here is only that.
 */
/** The receiver is chosen first, then its Boolean field decides the write. */
function selectedReceiver(
  flag: boolean,
  left: { value: boolean },
  right: { value: boolean },
): boolean {
  return ((flag ? left : right).value ||= true);
}
/** The key's effect happens once, before the read and the conditional write. */
function computedAnd(flag: boolean): boolean {
  const box: { value: boolean } = { value: flag };
  let count = 0;
  return (box[(count += 1) === 1 ? "value" : "value"] &&= false);
}
/** A nullish assignment to an element. */
function computedFallback(): number {
  const box: { value: number | null } = { value: null };
  let count = 0;
  return (box[(count += 1) === 1 ? "value" : "value"] ??= 1);
}
/** A nullish assignment to a field, whose kept arm is the present value. */
function fieldFallback(box: { value: number | null }): number {
  return (box.value ??= 0);
}
