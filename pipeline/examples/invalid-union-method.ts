// A number's `valueOf` gives a number, not the string the result states.
function value(x: string | number): string {
  return x.valueOf();
}
