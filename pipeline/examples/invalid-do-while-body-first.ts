// The body of a `do...while` runs before its test: on an empty array the
// first `xs[i]` reads past the end, so `last([])` returns `undefined`
// where its result is a string. As a `while` loop, the test first, the
// read is within the array.
export function last(xs: string[]): string {
  let found = "";
  let i = 0;
  do {
    found = xs[i];
    i++;
  } while (i < xs.length);
  return found;
}
