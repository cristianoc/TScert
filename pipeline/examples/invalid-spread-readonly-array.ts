// A spread of a readonly array into an object literal copies its own keys; a
// readonly array admits a host object, whose own keys are the host's
// internal fields: refused at the spread.
export function copy(xs: readonly number[]): object {
  return { ...xs };
}
