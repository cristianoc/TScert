// `new URL(input, base)` converts a URL base by `URL.prototype.toString`; a
// program replacing it changes what every input is resolved against (run
// under Node: `x` against `file:///tmp/dir/` gives `file:///elsewhere/x`):
// the global `URL` is read only as a constructor, refused.
export function replace(answer: () => string): void {
  URL.prototype.toString = answer;
}
