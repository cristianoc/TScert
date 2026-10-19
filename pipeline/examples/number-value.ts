// `Number` read as a value is the callable taking a primitive, converted
// without running code, and ignoring every further argument: `map` passes it
// each string with its index and the array, and stays dense.
export function parts(version: string): number[] {
  return version.split(".").map(Number);
}
