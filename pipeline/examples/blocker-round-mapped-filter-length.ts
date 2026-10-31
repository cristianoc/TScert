// A filter callback over arrays of inferred writable records.
// Census functions:
// written-applications.mts#writtenApplications
export function levels(
  xs: number[][],
): { name: number; bound: number | null }[][] {
  return xs
    .map((level) => level.map((name) => ({ name, bound: null })))
    .filter((level) => level.length);
}
