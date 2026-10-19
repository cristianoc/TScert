// `Number` read as a value takes a primitive: an object's conversion calls
// its `valueOf`, code of the client's, which may change the array `map`
// reads (run under Node: the result has a hole). Refused at the callback.
export function values(xs: object[]): number[] {
  return xs.map(Number);
}
