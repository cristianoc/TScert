// An object pattern's rest copies the operand's other own keys: of a record
// of readonly fields alone, which admits a host object, it is refused (R8,
// COMPILER-API.md).
export function rest(o: { readonly a: number; readonly b: string }): {} {
  const { a, ...r } = o;
  return r;
}
