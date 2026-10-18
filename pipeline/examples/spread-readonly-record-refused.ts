// A record of readonly fields alone admits a host object, whose stated
// members are views: a spread of it is refused (R8, COMPILER-API.md).
export function copy(o: { readonly a: number }): { a: number } {
  return { ...o };
}
