// `lib.augment.d.ts`, outside the project and named like a standard library
// file, declares another `assign` on `ObjectConstructor`. The compiler's
// library resolution does not give that file, so `Object.assign` is not the
// standard library's alone and is not the intrinsic copy. Under Node the
// call returns a `Number` object, not the string the declaration states.
export function assigned(): string {
  return Object.assign(1);
}
