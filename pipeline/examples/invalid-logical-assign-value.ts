// A `||=` keeps a truthy target: its value is any truthy number, not only
// the right side's (run under Node: `pick()` gives 2 after `count = 2`).
let count: number = 0;
export function set(n: number): void {
  count = n;
}
export function pick(): 1 {
  // @ts-expect-error a number is not 1
  return (count ||= 1);
}
