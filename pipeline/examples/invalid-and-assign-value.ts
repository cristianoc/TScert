// `&&=` of a number keeps a falsy target: its value is `0` or the right
// side's (run under Node: `pick()` gives 0).
let count: number = 0;
export function set(n: number): void {
  count = n;
}
export function pick(): 1 {
  // @ts-expect-error a number is not 1
  return (count &&= 1);
}
