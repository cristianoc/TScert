// `+` on a string-or-number and a number concatenates or adds: no one kind
// of result, refused.
function combine(x: string | number, y: number): string | number {
  return x + y;
}
