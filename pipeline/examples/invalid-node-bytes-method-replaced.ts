// A program replacing `Buffer.prototype.toString` changes what every
// `Buffer`'s `toString` answers (run under Node: a number):
// `Buffer.prototype` is outside the reviewed globals, refused.
export function replace(answer: () => string): void {
  Buffer.prototype.toString = answer;
}
