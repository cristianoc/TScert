// An array cannot own `toJSON`, which `JSON.stringify` would call (under Node
// an array owning `toJSON = () => undefined` stringifies to `undefined`): the
// contradictory input contract is refused rather than verified vacuously.
export function text(xs: number[] & { toJSON: () => undefined }): string {
  return JSON.stringify(xs);
}
