// A file of the project at `typescript/lib/lib.augment.d.ts` declares another
// `assign` on `ObjectConstructor`. Its path spells a standard library
// identity, but the compiler's library resolution does not give it, so
// `Object.assign` is not the standard library's alone and is not the
// intrinsic copy. Under Node the call returns a `Number` object, not the
// string the declaration states.
export function assigned(): string {
  return Object.assign(1);
}
