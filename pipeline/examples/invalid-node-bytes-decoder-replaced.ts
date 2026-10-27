// A program replacing `TextDecoder.prototype.decode` changes what every
// decoder answers (run under Node: a number): the global `TextDecoder` is
// read only as a constructor, refused.
export function replace(answer: () => string): void {
  TextDecoder.prototype.decode = answer;
}
