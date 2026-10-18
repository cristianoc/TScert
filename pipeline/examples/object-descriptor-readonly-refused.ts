// `Object.getOwnPropertyDescriptor` of a record of readonly fields alone,
// which admits a host object, is refused (R8, COMPILER-API.md).
export function descriptor(o: { readonly a: number }): boolean {
  return Object.getOwnPropertyDescriptor(o, "a") !== undefined;
}
