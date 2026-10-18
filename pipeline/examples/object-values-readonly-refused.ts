// A record of readonly fields alone admits a host object, whose own fields
// are the package's internal ones: `Object.values` of it is refused (R8,
// COMPILER-API.md).
interface R {
  readonly a: number;
}
export function values(o: R): number {
  return Object.values(o).length;
}
