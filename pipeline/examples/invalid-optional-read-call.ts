export function stale(
  obj: { val?: number | undefined },
  effect: () => void,
): undefined {
  if (obj.val === undefined) {
    effect();
    return obj.val;
  }
  return undefined;
}
