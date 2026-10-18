// `Object.assign` copies onto its target's own keys: onto a local annotated
// by readonly fields alone, which admits a host object, it is refused (R8,
// COMPILER-API.md).
export function assign(): number {
  const t: { readonly a: number } = { a: 1 };
  Object.assign(t, { b: 2 });
  return t.a;
}
