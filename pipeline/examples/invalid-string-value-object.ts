// `String` read as a value takes a primitive: an object's conversion calls
// its `toString`, code of the client's, which may change the array `map`
// reads (run under Node: the result has a hole). Refused at the callback.
export function texts(xs: object[]): string[] {
  return xs.map(String);
}
