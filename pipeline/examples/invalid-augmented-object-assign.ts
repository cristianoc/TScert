// Another module of the project augments `ObjectConstructor` with
// `assign(n: number): string`: `Object.assign` here is no longer the standard
// library's alone, so it is not the intrinsic copy. Under Node the call
// returns a `Number` object, not the string the augmentation states.
export function assigned(): string {
  return Object.assign(1);
}
