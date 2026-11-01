export function changed(Error: new () => { readonly code?: number }): number {
  const alias = new Error();
  Object.assign(new Error(), { code: "ENOENT" });
  return alias.code ?? 0;
}
