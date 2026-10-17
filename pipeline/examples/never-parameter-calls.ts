// A body whose parameter is of a type no value meets runs no node: each is
// within any footprint, a throw's included, whatever the call it makes.
export function unmatched(x: never): never {
  throw Error(`a value of no known constructor: ${JSON.stringify(x)}`);
}
export function largest(x: never): number {
  return Math.max(1, 2);
}
