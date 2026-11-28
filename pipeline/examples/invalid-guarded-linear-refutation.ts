// Without refuting `x >= 0`, `x <= 0` still permits `x === 0` with
// `obj.field === null`, so `obj.field.value` is refused (run under Node:
// `readWithoutGuard(0, { field: null })` throws TypeError).
type Holder = { field: { value: number } | null };

/** @requires safeInteger(x)
 *  @requires obj.field !== null || x >= 0
 */
export function readWithoutGuard(x: number, obj: Holder): number {
  if (x <= 0) {
    return obj.field!.value;
  }
  return x;
}
