// `new Array(n)` makes an array of length `n` with no elements: holes,
// which number[] forbids. The overlay reads `new Array` with no argument
// only, so the length constructor is refused.
function holes(n: number): number[] {
  return new Array(n);
}
