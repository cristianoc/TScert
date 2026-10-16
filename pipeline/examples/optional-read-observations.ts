export function absentOrUndefined(obj: { val?: number }): void {
  if (obj.val === undefined) {
    const u: undefined = obj.val;
  }
}
export function presentUndefined(obj: { val?: number | undefined }): undefined {
  if (obj.val === undefined) return obj.val;
  return undefined;
}
export function required(obj: { val: number | undefined }): undefined {
  if (obj.val === undefined) return obj.val;
  return undefined;
}
export function byTypeof(obj: { readonly val?: number }): undefined {
  if (typeof obj.val === "undefined") return obj.val;
  return undefined;
}
export function nullish(obj: { val?: number | null }): null | undefined {
  if (obj.val == null) return obj.val;
  return null;
}
export function falsy(obj: { val?: true }): undefined {
  if (!obj.val) return obj.val;
  return undefined;
}
export function allocatedBetween(obj: { val?: number }): undefined {
  if (obj.val === undefined) {
    const fresh: { count: number } = { count: 0 };
    return obj.val;
  }
  return undefined;
}
export function savedAcrossCall(
  obj: { val?: number },
  effect: () => void,
): undefined {
  const saved = obj.val;
  if (saved === undefined) {
    effect();
    return saved;
  }
  return undefined;
}
export function observeOnly(obj: { val?: number }): number {
  if (obj.val === undefined) return 0;
  return 1;
}
