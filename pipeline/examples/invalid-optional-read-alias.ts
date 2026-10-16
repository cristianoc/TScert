export function stale(obj: { val: number | undefined }): undefined {
  const alias = obj;
  if (obj.val === undefined) {
    alias.val = 1;
    return obj.val;
  }
  return undefined;
}
