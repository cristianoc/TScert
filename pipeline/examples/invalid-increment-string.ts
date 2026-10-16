// `s++` converts a string to a number; it is not a concatenation: refused.
function next(): string {
  let s: string = "1";
  s++;
  return s;
}
